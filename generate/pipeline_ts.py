#!/usr/bin/env python3
"""
Pipeline: 直接通过 typegraph.json 将 JS 转为 .ts。

对每个包运行 ast2type 管线（std 或 agent），从 typegraph.json 提取
函数签名，按 typegraph 的文件和源码位置织入 JS，生成 .ts 文件并保持原目录结构。

不经过 .d.ts 中转 —— 直接使用管道内部的类型推断结果。

用法:
  python3 generate/pipeline_ts.py \
      --source-dir tests/typeweaver \
      --output-dir output_ts

  python3 generate/pipeline_ts.py \
      --source-dir tests/typeweaver \
      --output-dir output_ts \
      --packages ansi-regex,abab
"""
import argparse, json, os, re, shutil, subprocess, sys, time
from collections import Counter

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT_DIR = os.path.normpath(os.path.join(SCRIPT_DIR, ".."))
MAKE_SH = os.path.join(ROOT_DIR, "make.sh")
OUT_DIR = os.path.join(ROOT_DIR, "output")

if ROOT_DIR not in sys.path:
    sys.path.insert(0, ROOT_DIR)

from generate.weave import (
    _inject_class_fields,
    _normalize_default_export_assignments,
    _sanitize_ts_type,
    _split_function_arrow,
)
from generate.weave_typegraph_ast import (
    TypegraphWeaveError,
    weave_typegraph_package,
)


# ==================== 类型转换: pipeline typegraph → TypeScript ====================

def _is_template_literal(s):
    """检查字符串是否是模板字面量 (以反引号包围)."""
    return isinstance(s, str) and s.startswith("`") and s.endswith("`")


def _has_top_level_union_or_intersection(ts_type):
    """Return whether an array element type needs grouping before ``[]``."""
    depth = 0
    quote = None
    escaped = False
    for character in ts_type:
        if quote:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == quote:
                quote = None
            continue
        if character in "'\"`":
            quote = character
        elif character in "([{<":
            depth += 1
        elif character in ")]}>" and depth:
            depth -= 1
        elif depth == 0 and character in "|&":
            return True
    return False


def _full_type_to_ts(ft):
    """将 pipeline fullType JSON 转换为 TypeScript 类型字符串。

    Args:
        ft: fullType JSON 对象或普通字符串

    Returns:
        TypeScript 类型字符串
    """
    if isinstance(ft, str):
        # 直接是类型名字符串
        if ft == "undefined":
            return "undefined"
        if ft == "unknown":
            return "any"
        if ft == "PromiseConstructor":
            return "Promise<any>"
        if not ft or re.match(r'^obj_\d+$', ft):
            return "any"
        # constructor 类型: "new (params) : RetType" → any
        if ft.startswith("new ") or re.match(r'^new\s*\(', ft):
            return "any"
        # 函数返回类型语法 "): Type" — 不是合法 TS 类型 → any
        if re.search(r'\)\s*:\s+\w', ft):
            return "any"
        return _sanitize_ts_type(ft)

    if not isinstance(ft, dict):
        return "any"

    kind = ft.get("kind", "unknown")

    if kind == "primitive":
        name = ft.get("name", "unknown")
        if name == "undefined":
            return "undefined"
        if name == "unknown":
            return "any"
        return name  # string, number, boolean

    if kind == "literal":
        val = ft.get("value")
        if ft.get("valueKind") == "bigint" and isinstance(val, str):
            bigint_literal = (
                r'^(?:\d+|0[xX][0-9a-fA-F]+|0[bB][01]+|0[oO][0-7]+)n$'
            )
            return val if re.match(bigint_literal, val) else "bigint"
        if val is None:
            return "null"
        if isinstance(val, bool):
            return "true" if val else "false"
        if isinstance(val, (int, float)):
            return str(val)
        if isinstance(val, str):
            if _is_template_literal(val):
                # 模板字面量 → 基础类型 string
                return "string"
            # 普通字符串 → 字符串字面量类型
            return json.dumps(val)  # 带引号的字符串
        return "any"

    if kind == "union":
        types = ft.get("types", [])
        parts = []
        for t in types:
            ts = _full_type_to_ts(t)
            if ts and ts != "undefined":
                parts.append(ts)
        if not parts:
            return "undefined"
        if len(parts) == 1:
            return parts[0]
        return " | ".join(parts)

    if kind == "object":
        name = ft.get("name", "object")
        properties = ft.get("properties", {})
        if properties:
            members = []
            for key, value in properties.items():
                rendered_key = key if re.match(r'^[A-Za-z_$][\w$]*$', key) else json.dumps(key)
                members.append(f"{rendered_key}: {_full_type_to_ts(value)}")
            return "{ " + "; ".join(members) + " }"
        # 匿名对象 (obj_XXX) → object
        if not name or name == "object" or re.match(r'^obj_\d+$', name):
            return "any"
        return name  # RegExp, Date, etc.

    if kind == "function":
        params = ft.get("params", [])
        ret = _full_type_to_ts(ft.get("returnType", {"kind": "primitive", "name": "void"}))
        param_parts = []
        for p in params:
            pname = p.get("name", "arg")
            ptype = _full_type_to_ts(p.get("type", {"kind": "primitive", "name": "any"}))
            param_parts.append(f"{pname}: {ptype}")
        return f"({', '.join(param_parts)}) => {ret}"

    # 数组等
    if kind == "array":
        elem = _full_type_to_ts(ft.get("elementType", {"kind": "primitive", "name": "any"}))
        if (_split_function_arrow(elem) is not None
                or _has_top_level_union_or_intersection(elem)):
            elem = f"({elem})"
        return f"{elem}[]"

    return "any"


# ==================== typegraph 解析 ====================

def _load_typegraph(output_dir):
    """加载 typegraph.json。"""
    tg_path = os.path.join(output_dir, "typegraph.json")
    if not os.path.isfile(tg_path):
        return None
    with open(tg_path) as f:
        return json.load(f)


def _extract_exports_from_typegraph(typegraph):
    """从 typegraph 提取导出符号的类型签名。

    查找所有具名函数节点, 按 name 去重 (同名的只保留第一个)。

    Returns:
        [{name, kind, inferred}, ...]
        inferred 格式: "(param1: Type1, param2: Type2) => ReturnType"
    """
    exports = []
    seen = set()

    for node in typegraph.get("nodes", []):
        ft_str = node.get("fullType", "")
        if not ft_str:
            continue
        try:
            ft = json.loads(ft_str)
        except (json.JSONDecodeError, TypeError):
            continue

        kind = ft.get("kind", "")
        name = ft.get("name", "")

        # 跳过匿名函数
        if not name or name in seen:
            continue

        if kind == "function":
            # 构建 inferred 签名
            params = ft.get("params", [])
            param_parts = []
            for p in params:
                pname = p.get("name", "arg")
                ptype = _full_type_to_ts(p.get("type", {"kind": "primitive", "name": "any"}))
                param_parts.append(f"{pname}: {ptype}")
            params_str = ", ".join(param_parts)
            ret_type = _full_type_to_ts(ft.get("returnType", {"kind": "primitive", "name": "void"}))
            inferred = f"({params_str}) => {ret_type}"

            seen.add(name)
            exports.append({
                "name": name,
                "kind": "function",
                "inferred": inferred,
            })

    return exports


# ==================== 包发现 ====================

def discover_packages(source_dir):
    """发现所有包含 .js 或 .mjs 文件的包目录。"""
    pkgs = []
    if not os.path.isdir(source_dir):
        return pkgs
    for name in sorted(os.listdir(source_dir)):
        d = os.path.join(source_dir, name)
        if not os.path.isdir(d):
            continue
        if name in ("results",) or name.endswith("_output") or name.endswith("_erase"):
            continue
        if any(f.endswith((".js", ".mjs")) for f in os.listdir(d)):
            pkgs.append(name)
    return pkgs


# ==================== 主流程 ====================

def run_pipeline(
    pkg_dir,
    timeout=600,
    inference_mode="agent",
    inference_output_dir=None,
    agent_candidate_mode="fair",
    agent_provider=None,
    agent_model=None,
    agent_base_url=None,
):
    """Run inference from fresh package artifacts or raise on failure."""
    if inference_mode not in {"std", "agent"}:
        raise ValueError(f"unsupported inference mode: {inference_mode}")

    inference_output_dir = os.path.abspath(inference_output_dir or OUT_DIR)
    # Each package starts from an empty inference directory. This prevents a
    # failed package from accidentally reusing the previous package's graph.
    if os.path.isdir(inference_output_dir):
        shutil.rmtree(inference_output_dir)

    cmd = [
        MAKE_SH,
        pkg_dir,
        "--js",
        "--prepare",
        "--output-dir",
        inference_output_dir,
    ]
    if inference_mode == "agent":
        cmd.extend(["--agent", "--agent-candidate-mode", agent_candidate_mode])
        if agent_provider:
            cmd.extend(["--agent-provider", agent_provider])
        if agent_model:
            cmd.extend(["--agent-model", agent_model])
        if agent_base_url:
            cmd.extend(["--agent-base-url", agent_base_url])
    print(f"  cmd: {' '.join(cmd)}")
    proc = subprocess.run(cmd, cwd=ROOT_DIR, capture_output=False, timeout=timeout)
    if proc.returncode != 0:
        raise RuntimeError(f"make.sh exited with status {proc.returncode}")


def _check_all_ts_exist(pkg_dir, pkg_out_dir):
    """检查是否所有 .js 和 .mjs 文件都已有对应的 .ts 文件。"""
    js_files = []
    for root, dirs, files in os.walk(pkg_dir):
        dirs[:] = [d for d in dirs if d not in ("node_modules", ".git")]
        for f in files:
            if f.endswith((".js", ".mjs")):
                rel = os.path.relpath(os.path.join(root, f), pkg_dir)
                js_files.append(rel)
    if not js_files:
        return False
    for rel in js_files:
        ts_rel = os.path.splitext(rel)[0] + ".ts"
        if not os.path.isfile(os.path.join(pkg_out_dir, ts_rel)):
            return False
    return True


def _inject_node_globals(ts_files):
    """为引用 Node.js 全局变量的 .ts 文件注入 declare 声明。"""
    globals_map = {
        "exports": "var exports: any",
        "module": "var module: { exports: any; [key: string]: any }",
        "process": "var process: any",
        "Buffer": "var Buffer: any",
        "__dirname": "var __dirname: string",
        "__filename": "var __filename: string",
        "global": "var global: any",
        "define": "function define(...args: any[]): any",
        "require": "function require(name: string): any",
    }
    fixed = 0
    for ts_path in ts_files:
        try:
            with open(ts_path, encoding="utf-8") as f:
                content = f.read()
        except (IOError, OSError):
            continue
        needed = []
        for name, decl in globals_map.items():
            if re.search(r'\b' + re.escape(name) + r'\b', content):
                local_declaration = re.search(
                    r'\b(declare|var|let|const|function)\s+' + re.escape(name) + r'\b',
                    content,
                )
                imported = re.search(
                    r'^\s*import\s+(?:type\s+)?[^;\n]*\b' + re.escape(name) + r'\b',
                    content,
                    re.MULTILINE,
                )
                if not local_declaration and not imported:
                    needed.append(decl)
        if not needed:
            continue
        lines = content.splitlines(keepends=True)
        insert_at = 0
        if lines and lines[0].strip().startswith("#!"):
            insert_at = 1
            if len(lines) > 1 and lines[1].strip() == "":
                insert_at = 2
        if insert_at < len(lines):
            stripped = lines[insert_at].strip()
            if stripped.startswith('"use strict"') or stripped.startswith("'use strict'"):
                insert_at += 1
                if insert_at < len(lines) and lines[insert_at].strip() == "":
                    insert_at += 1
        decl_block = ";\n".join("declare " + d for d in needed) + ";\n"
        lines.insert(insert_at, decl_block)
        try:
            with open(ts_path, "w", encoding="utf-8") as f:
                f.writelines(lines)
            fixed += 1
        except (IOError, OSError):
            pass
    return fixed


def _write_weave_report(pkg_out_dir, report):
    os.makedirs(pkg_out_dir, exist_ok=True)
    report_path = os.path.join(pkg_out_dir, "ast2type-weave-report.json")
    with open(report_path, "w", encoding="utf-8") as report_file:
        json.dump(report, report_file, indent=2, ensure_ascii=False)
        report_file.write("\n")


def _weave_summary(pkg_out_dir):
    report_path = os.path.join(pkg_out_dir, "ast2type-weave-report.json")
    if not os.path.isfile(report_path):
        return None
    try:
        with open(report_path, encoding="utf-8") as report_file:
            report = json.load(report_file)
    except (OSError, json.JSONDecodeError):
        return None
    reasons = Counter(
        item.get("reason", "unknown")
        for item in report.get("skipped", [])
        if isinstance(item, dict)
    )
    return {
        key: report.get(key, 0)
        for key in (
            "function_nodes",
            "canonical_targets",
            "ignored_noncanonical",
            "ignored_duplicate_canonical",
            "located_targets",
            "woven_targets",
            "edits",
            "skipped_targets",
            "modified_files",
            "compatibility_normalized_files",
            "node_global_declaration_files",
        )
    } | {"skipped_reasons": dict(sorted(reasons.items()))}


def generate_ts_for_pkg(
    pkg_dir,
    pkg_name,
    output_dir,
    cleanup=True,
    skip_existing=True,
    timeout=600,
    inference_mode="agent",
    agent_candidate_mode="fair",
    agent_provider=None,
    agent_model=None,
    agent_base_url=None,
):
    """对单个包运行管线 → 提取类型 → 织入 → 写 .ts。

    Returns:
        (status, file_count, errors)
    """
    print(f"\n{'='*60}")
    print(f"  Pipeline TS: {pkg_name}")
    print(f"  源目录: {pkg_dir}")
    print(f"{'='*60}")

    pkg_out_dir = os.path.join(output_dir, pkg_name)

    # 跳过已有 .ts
    if skip_existing and _check_all_ts_exist(pkg_dir, pkg_out_dir):
        js_files = []
        for root, dirs, files in os.walk(pkg_dir):
            dirs[:] = [d for d in dirs if d not in ("node_modules", ".git")]
            for f in files:
                if f.endswith((".js", ".mjs")):
                    js_files.append(f)
        print(f"  跳过 ({len(js_files)} 个 .ts 已存在)")
        return ("skipped", len(js_files), [])

    # Regeneration must not leave files that disappeared from the source package.
    if os.path.isdir(pkg_out_dir):
        shutil.rmtree(pkg_out_dir)

    # 1. 运行管线
    inference_output_dir = os.path.join(
        os.path.abspath(output_dir), ".inference", pkg_name
    )
    try:
        run_pipeline(
            pkg_dir,
            timeout=timeout,
            inference_mode=inference_mode,
            inference_output_dir=inference_output_dir,
            agent_candidate_mode=agent_candidate_mode,
            agent_provider=agent_provider,
            agent_model=agent_model,
            agent_base_url=agent_base_url,
        )
    except subprocess.TimeoutExpired:
        message = f"pipeline timed out after {timeout}s"
        print(f"  ⚠ {message}")
        return ("failed", 0, [message])
    except (OSError, RuntimeError) as error:
        message = str(error)
        print(f"  ⚠ {message}")
        return ("failed", 0, [message])

    # 2. 从 typegraph 提取类型
    typegraph = _load_typegraph(inference_output_dir)
    if not typegraph:
        print(f"  ⚠ 未生成 typegraph.json, 跳过")
        return ("failed", 0, ["no typegraph"])

    # 3. 仅使用 canonical 函数节点，并按 file + position 精确写回。
    try:
        woven, weave_report = weave_typegraph_package(
            pkg_dir,
            typegraph,
            render_type=_full_type_to_ts,
        )
    except (OSError, TypegraphWeaveError) as error:
        message = f"AST weave failed: {error}"
        print(f"  ⚠ {message}")
        return ("failed", 0, [message])
    if not woven:
        return ("skipped", 0, ["no JavaScript files"])
    print(
        "  AST 编织: "
        f"目标 {weave_report['canonical_targets']}, "
        f"命中 {weave_report['located_targets']}, "
        f"跳过 {weave_report['skipped_targets']}, "
        f"编辑 {weave_report['edits']}"
    )
    if (weave_report["canonical_targets"] > 0
            and weave_report["located_targets"] == 0):
        message = "AST weave located 0 canonical targets"
        weave_report["validation_error"] = message
        _write_weave_report(pkg_out_dir, weave_report)
        print(f"  ⚠ {message}")
        return ("failed", 0, [message])

    # 4. 写入输出目录 (保持原目录结构, 改后缀 .js → .ts)
    count = 0
    normalized_files = 0
    for rel, content in woven.items():
        ts_rel = os.path.splitext(rel)[0] + ".ts"
        ts_path = os.path.join(pkg_out_dir, ts_rel)
        os.makedirs(os.path.dirname(ts_path), exist_ok=True)
        # These compatibility transforms address JS class/export constructs;
        # function annotation placement itself is exclusively AST-positioned.
        normalized = _inject_class_fields(
            _normalize_default_export_assignments(content)
        )
        if normalized != content:
            normalized_files += 1
        with open(ts_path, "w", encoding="utf-8") as f:
            f.write(normalized)
        count += 1

    print(f"  生成 {count} 个 .ts 文件 → {pkg_out_dir}/")

    # 4.5. 注入 Node.js 全局变量 declare 声明
    ts_files = []
    for root, dirs, files in os.walk(pkg_out_dir):
        dirs[:] = [d for d in dirs if d not in ("node_modules", ".git")]
        for f in files:
            if f.endswith(".ts") and not f.endswith(".d.ts"):
                ts_files.append(os.path.join(root, f))
    ng_fixed = _inject_node_globals(ts_files)
    if ng_fixed:
        print(f"  注入 Node.js 全局声明: {ng_fixed} 文件")

    weave_report["compatibility_normalized_files"] = normalized_files
    weave_report["node_global_declaration_files"] = ng_fixed
    _write_weave_report(pkg_out_dir, weave_report)

    # 5. 清理
    if cleanup:
        shutil.rmtree(inference_output_dir, ignore_errors=True)
        inference_parent = os.path.dirname(inference_output_dir)
        try:
            os.rmdir(inference_parent)
        except OSError:
            pass

    return ("ok", count, [])


def main():
    parser = argparse.ArgumentParser(
        description="Pipeline: JS → .ts (通过 ast2type typegraph 直接织入)"
    )
    parser.add_argument("--source-dir", required=True,
                        help="包含 JS 包的目录")
    parser.add_argument("--output-dir", required=True,
                        help="输出 .ts 文件的目录")
    parser.add_argument("--packages",
                        help="逗号分隔的包名列表 (默认: 自动发现)")
    parser.add_argument("--timeout", type=int, default=600,
                        help="每个包的管线超时秒数 (默认 600)")
    parser.add_argument("--inference-mode", choices=("std", "agent"),
                        default="agent",
                        help="推断模式（默认 agent，正式实验应显式指定）")
    parser.add_argument("--agent-candidate-mode", choices=("fair", "gt"),
                        default="fair",
                        help="Agent 候选模式（TypeWeaver 评测使用 fair）")
    parser.add_argument("--agent-provider", choices=("deepseek", "openai"),
                        help="Agent API provider（默认由环境变量决定）")
    parser.add_argument("--agent-model",
                        help="覆盖 provider 默认模型")
    parser.add_argument("--agent-base-url",
                        help="覆盖 provider API base URL")
    parser.add_argument("--no-cleanup", action="store_true",
                        help="保留 make.sh 中间产物")
    parser.add_argument("--no-skip", action="store_true",
                        help="即使 .ts 已存在也重新生成")
    parser.add_argument("--results-file",
                        help="逐包生成结果 JSON（默认输出目录/pipeline-results.json）")
    args = parser.parse_args()

    if args.inference_mode == "std" and any((
        args.agent_provider,
        args.agent_model,
        args.agent_base_url,
    )):
        parser.error("std 模式不能使用 agent provider/model/base URL 参数")

    source_dir = os.path.abspath(args.source_dir)
    output_dir = os.path.abspath(args.output_dir)
    os.makedirs(output_dir, exist_ok=True)

    if args.packages:
        packages = [p.strip() for p in args.packages.split(",") if p.strip()]
    else:
        packages = discover_packages(source_dir)

    if not packages:
        print(f"错误: 在 {source_dir} 未找到任何 JS 包")
        sys.exit(1)

    print("=" * 60)
    print("  Pipeline .ts 生成 (typegraph 直接织入)")
    print(f"  源目录:   {source_dir}")
    print(f"  输出目录: {output_dir}")
    print(f"  包数量:   {len(packages)}")
    print(f"  推断模式: {args.inference_mode}")
    print(f"  包列表:   {', '.join(packages)}")
    print("=" * 60)

    total_start = time.time()
    results = []

    for idx, pkg_name in enumerate(packages):
        pkg_dir = os.path.join(source_dir, pkg_name)
        if not os.path.isdir(pkg_dir):
            print(f"  [{idx+1}/{len(packages)}] {pkg_name} — 目录不存在, 跳过")
            results.append((
                pkg_name, "failed", 0, ["source directory missing"], None
            ))
            continue

        status, count, errors = generate_ts_for_pkg(
            pkg_dir, pkg_name, output_dir,
            cleanup=not args.no_cleanup,
            skip_existing=not args.no_skip,
            timeout=args.timeout,
            inference_mode=args.inference_mode,
            agent_candidate_mode=args.agent_candidate_mode,
            agent_provider=args.agent_provider,
            agent_model=args.agent_model,
            agent_base_url=args.agent_base_url,
        )
        results.append((
            pkg_name,
            status,
            count,
            errors,
            _weave_summary(os.path.join(output_dir, pkg_name)),
        ))

    elapsed = time.time() - total_start

    print(f"\n{'='*60}")
    print(f"  完成, 耗时 {elapsed:.0f}s")
    print(f"{'='*60}")
    print(f"  {'Package':<24} {'Status':<10} {'Files':>6}")
    print(f"  {'-'*42}")
    ok = fail = skipped = 0
    for pkg, status, count, _errors, _weave in results:
        print(f"  {pkg:<24} {status:<10} {count:>6}")
        if status == "ok":
            ok += 1
        elif status == "skipped":
            skipped += 1
        else:
            fail += 1
    print(f"\n  {ok} ok, {skipped} skipped, {fail} failed")
    print(f"  输出: {output_dir}")

    results_path = os.path.abspath(
        args.results_file or os.path.join(output_dir, "pipeline-results.json")
    )
    os.makedirs(os.path.dirname(results_path), exist_ok=True)
    with open(results_path, "w", encoding="utf-8") as result_file:
        json.dump({
            "schema": 1,
            "inference_mode": args.inference_mode,
            "agent_candidate_mode": (
                args.agent_candidate_mode if args.inference_mode == "agent" else None
            ),
            "elapsed_seconds": round(elapsed, 6),
            "counts": {"ok": ok, "skipped": skipped, "failed": fail},
            "results": [
                {
                    "package": pkg,
                    "status": status,
                    "files": count,
                    "errors": errors,
                    "weave": weave,
                }
                for pkg, status, count, errors, weave in results
            ],
        }, result_file, indent=2)
        result_file.write("\n")
    print(f"  生成记录: {results_path}")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
