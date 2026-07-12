#!/usr/bin/env python3
"""
Pipeline: 直接通过 typegraph.json 将 JS 转为 .ts。

对每个包运行 ast2type 管线 (make.sh --agent)，从 typegraph.json 提取
函数签名和变量类型，直接织入 JS 源码生成 .ts 文件，保持原目录结构。

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

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT_DIR = os.path.normpath(os.path.join(SCRIPT_DIR, ".."))
MAKE_SH = os.path.join(ROOT_DIR, "make.sh")
OUT_DIR = os.path.join(ROOT_DIR, "output")

if ROOT_DIR not in sys.path:
    sys.path.insert(0, ROOT_DIR)

from generate.weave import _sanitize_ts_type, weave_package


# ==================== 类型转换: pipeline typegraph → TypeScript ====================

def _is_template_literal(s):
    """检查字符串是否是模板字面量 (以反引号包围)."""
    return isinstance(s, str) and s.startswith("`") and s.endswith("`")


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

def run_pipeline(pkg_dir, timeout=600):
    """Run inference from fresh package artifacts or raise on failure."""
    typegraph_path = os.path.join(OUT_DIR, "typegraph.json")
    if os.path.isfile(typegraph_path):
        os.remove(typegraph_path)

    package_output = f"{pkg_dir}_output"
    if os.path.isdir(package_output):
        shutil.rmtree(package_output)

    cmd = [MAKE_SH, pkg_dir, "--js", "--prepare", "--agent"]
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


def generate_ts_for_pkg(
    pkg_dir,
    pkg_name,
    output_dir,
    cleanup=True,
    skip_existing=True,
    timeout=600,
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
    try:
        run_pipeline(pkg_dir, timeout=timeout)
    except subprocess.TimeoutExpired:
        message = f"pipeline timed out after {timeout}s"
        print(f"  ⚠ {message}")
        return ("failed", 0, [message])
    except (OSError, RuntimeError) as error:
        message = str(error)
        print(f"  ⚠ {message}")
        return ("failed", 0, [message])

    # 2. 从 typegraph 提取类型
    typegraph = _load_typegraph(OUT_DIR)
    if not typegraph:
        print(f"  ⚠ 未生成 typegraph.json, 跳过")
        return ("failed", 0, ["no typegraph"])

    exports = _extract_exports_from_typegraph(typegraph)
    if not exports:
        print("  typegraph 中无具名函数, 原样迁移 JS/MJS")
    else:
        print(f"  从 typegraph 提取 {len(exports)} 个类型:")
        for e in exports[:10]:
            print(f"    {e['name']}: {e['inferred']}")
        if len(exports) > 10:
            print(f"    ... 还有 {len(exports) - 10} 个")

    # 3. 织入 JS → .ts
    woven = weave_package(pkg_dir, exports)
    if not woven:
        return ("skipped", 0, ["no JavaScript files"])

    # 4. 写入输出目录 (保持原目录结构, 改后缀 .js → .ts)
    count = 0
    for rel, content in woven.items():
        ts_rel = os.path.splitext(rel)[0] + ".ts"
        ts_path = os.path.join(pkg_out_dir, ts_rel)
        os.makedirs(os.path.dirname(ts_path), exist_ok=True)
        with open(ts_path, "w", encoding="utf-8") as f:
            f.write(content)
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

    # 5. 清理
    if cleanup:
        shutil.rmtree(OUT_DIR, ignore_errors=True)
        out_suffix = f"{pkg_dir}_output"
        if os.path.isdir(out_suffix):
            shutil.rmtree(out_suffix, ignore_errors=True)

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
    parser.add_argument("--no-cleanup", action="store_true",
                        help="保留 make.sh 中间产物")
    parser.add_argument("--no-skip", action="store_true",
                        help="即使 .ts 已存在也重新生成")
    args = parser.parse_args()

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
    print(f"  包列表:   {', '.join(packages)}")
    print("=" * 60)

    total_start = time.time()
    results = []

    for idx, pkg_name in enumerate(packages):
        pkg_dir = os.path.join(source_dir, pkg_name)
        if not os.path.isdir(pkg_dir):
            print(f"  [{idx+1}/{len(packages)}] {pkg_name} — 目录不存在, 跳过")
            results.append((pkg_name, "skipped", 0))
            continue

        status, count, errors = generate_ts_for_pkg(
            pkg_dir, pkg_name, output_dir,
            cleanup=not args.no_cleanup,
            skip_existing=not args.no_skip,
            timeout=args.timeout,
        )
        results.append((pkg_name, status, count))

    elapsed = time.time() - total_start

    print(f"\n{'='*60}")
    print(f"  完成, 耗时 {elapsed:.0f}s")
    print(f"{'='*60}")
    print(f"  {'Package':<24} {'Status':<10} {'Files':>6}")
    print(f"  {'-'*42}")
    ok = fail = skipped = 0
    for pkg, status, count in results:
        print(f"  {pkg:<24} {status:<10} {count:>6}")
        if status == "ok":
            ok += 1
        elif status == "skipped":
            skipped += 1
        else:
            fail += 1
    print(f"\n  {ok} ok, {skipped} skipped, {fail} failed")
    print(f"  输出: {output_dir}")


if __name__ == "__main__":
    main()
