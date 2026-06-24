#!/usr/bin/env python3
"""
类型织入: 将推断的类型注解插入 JS 源码，生成 TypeScript。

从 JS 源码 + 类型信息 → .ts 文件。

用法:
  from generate.weave import weave_package, parse_dts_exports

  exports = parse_dts_exports("path/to/index.d.ts")
  woven = weave_package("path/to/pkg", exports)
  # woven = {"rel/path.ts": "typescript content"}
"""
import os, re


# ==================== .d.ts 解析 ====================

def _strip_comments(content):
    content = re.sub(r'/\*\*[\s\S]*?\*/', '', content)
    content = re.sub(r'//[^\n]*', '', content)
    return content


def _collapse_ws(s):
    return re.sub(r'\s+', ' ', s).strip()


def parse_dts_exports(dts_path):
    """解析 .d.ts 文件，返回 exports 列表 [{name, kind, inferred}]。

    从 declare function / declare var / export function / export default 等
    提取导出符号及其类型。inferred 格式:
      - function: "(param1: Type1, param2: Type2) => ReturnType"
      - variable: "TypeName"
    """
    if not os.path.exists(dts_path):
        return []

    with open(dts_path) as f:
        raw = f.read()

    content = _strip_comments(raw)
    flat = _collapse_ws(content)
    # 在关键位置插入换行，方便逐行匹配
    flat = re.sub(r'\b(export\s|declare\s)', r'\n\1', flat).strip()

    exports = []
    seen = set()

    # export function name(params): RetType
    func_pat = r'export\s+(?:default\s+)?function\s+(\w+)\s*(?:<[^>]*>)?\s*\(([^)]*)\)\s*:\s*(\S[^;\n]+?)\s*(?:;|$)'
    for m in re.finditer(func_pat, flat, re.MULTILINE):
        name = m.group(1)
        params = m.group(2).strip()
        ret = m.group(3).strip().rstrip(";").strip()
        if name not in seen:
            seen.add(name)
            exports.append({
                "name": name, "kind": "function",
                "inferred": f"({params}) => {ret}"
            })

    # declare function name(params): RetType
    for m in re.finditer(r'declare\s+function\s+(\w+)\s*(?:<[^>]*>)?\s*\(([^)]*)\)\s*:\s*(\S[^;\n]+?)\s*(?:;|$)', flat, re.MULTILINE):
        name = m.group(1)
        params = m.group(2).strip()
        ret = m.group(3).strip().rstrip(";").strip()
        if name not in seen:
            seen.add(name)
            exports.append({
                "name": name, "kind": "function",
                "inferred": f"({params}) => {ret}"
            })

    # declare var/const name: Type
    declare_vars = {}
    for m in re.finditer(r'declare\s+(?:const|var)\s+(\w+)\s*:\s*([^;\n]+?)\s*(?:;|$)', flat, re.MULTILINE):
        declare_vars[m.group(1)] = m.group(2).strip().rstrip(";").strip()

    # export = cjsName
    cjs_match = re.search(r'export\s*=\s*(\w+)\s*(?:;|$)', flat, re.MULTILINE)
    if cjs_match:
        cjs_name = cjs_match.group(1)
        if cjs_name in declare_vars and cjs_name not in seen:
            seen.add(cjs_name)
            exports.append({
                "name": cjs_name, "kind": "variable",
                "inferred": declare_vars[cjs_name]
            })

    # export default name
    default_match = re.search(r'export\s+default\s+(\w+)\s*(?:;|$)', flat, re.MULTILINE)
    if default_match:
        def_name = default_match.group(1)
        if def_name in declare_vars and def_name not in seen:
            seen.add(def_name)
            exports.append({
                "name": def_name, "kind": "variable",
                "inferred": declare_vars[def_name]
            })

    # export const/var name = Type / name: Type
    if not exports:
        for m in re.finditer(r'export\s+(?:const|var)\s+(\w+)\s*[=:]\s*([^;\n]+?)\s*(?:;|$)', flat, re.MULTILINE):
            name = m.group(1)
            if name not in seen:
                seen.add(name)
                exports.append({
                    "name": name, "kind": "variable",
                    "inferred": m.group(2).strip().rstrip(";").strip()
                })

    return exports


# ==================== 类型解析 ====================

def _parse_inferred_params(inferred):
    """从 '(a: T1, b: T2) => R' 或 '() => R' 提取参数类型列表和返回类型。"""
    if "=>" not in inferred:
        return [], inferred.strip()
    sig, ret = inferred.split("=>", 1)
    sig = sig.strip()
    ret = ret.strip()
    if sig.startswith("(") and sig.endswith(")"):
        sig = sig[1:-1]
    param_types = []
    if sig.strip():
        for p in sig.split(","):
            p = p.strip()
            if ":" in p:
                param_types.append(p.split(":", 1)[1].strip())
            elif p == "..." or p.startswith("..."):
                param_types.append("any[]")
            else:
                param_types.append("any")
    return param_types, ret


def _split_params(params_str):
    """按逗号分割参数列表，忽略 {} [] 内的逗号。"""
    parts = []
    depth = 0  # { or [ nesting
    current = []
    for ch in params_str:
        if ch in "{[":
            depth += 1
        elif ch in "}]":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    if current:
        parts.append("".join(current).strip())
    return [p for p in parts if p]


# ==================== 类型织入 ====================

def _weave_signature(source, func_name, inferred):
    """在源码中为指定函数织入参数类型和返回类型。

    返回修改后的源码。若未找到匹配则返回原源码。
    """
    param_types, ret_type = _parse_inferred_params(inferred)

    prefix = (
        r'(?:export\s+default\s+|export\s+|module\.exports\s*=\s*|'
        rf'(?:const|var|let)\s+{re.escape(func_name)}\s*=\s*)?'
        rf'function\s+{re.escape(func_name)}\s*'
    )
    pat = re.compile(
        rf'({prefix})'
        r'\(([^)]*)\)'
        r'(\s*\{)',
    )

    m = pat.search(source)
    if not m:
        # 箭头函数带大括号: const fn = (x) => { ... }
        pat2 = re.compile(
            rf'((?:const|var|let)\s+{re.escape(func_name)}\s*=\s*)'
            rf'\(([^)]*)\)'
            rf'(\s*=>\s*\{{)',
            re.DOTALL
        )
        m = pat2.search(source)
        if not m:
            # 箭头函数无大括号: const fn = (x) => expr
            pat3 = re.compile(
                rf'((?:const|var|let)\s+{re.escape(func_name)}\s*=\s*)'
                rf'\(([^)]*)\)'
                rf'(\s*=>\s+)',
                re.DOTALL
            )
            m = pat3.search(source)
            if not m:
                # 箭头函数单参数无括号: const fn = x => expr
                pat4 = re.compile(
                    rf'((?:const|var|let)\s+{re.escape(func_name)}\s*=\s*)'
                    rf'(\w+(?:\s*:\s*\S+)?)'
                    rf'(\s*=>\s+)',
                    re.DOTALL
                )
                m = pat4.search(source)
                if not m:
                    return None  # 未匹配

    prefix_val = m.group(1)
    params_str = m.group(2)
    suffix = m.group(3)

    # 织入参数类型
    if param_types and params_str.strip():
        # 按逗号分割但忽略 {} 和 [] 内的逗号
        source_params = _split_params(params_str)
        typed_params = []
        for i, sp in enumerate(source_params):
            if not sp:
                typed_params.append(sp)
                continue
            name_m = re.match(r'(\w+)', sp)
            if name_m and i < len(param_types):
                pname = name_m.group(1)
                rest = sp[name_m.end():]
                typed_params.append(f"{pname}: {param_types[i]}{rest}")
            elif sp.startswith("{"):
                # 解构参数: {a, b} = default → {a, b}: Type = default
                dest_m = re.match(r'(\{[^}]*\})', sp)
                if dest_m and i < len(param_types):
                    pattern_part = dest_m.group(1)
                    rest = sp[dest_m.end():]
                    typed_params.append(f"{pattern_part}: {param_types[i]}{rest}")
                else:
                    typed_params.append(sp)
            elif sp.startswith("["):
                # 数组解构: [a, b] = default → [a, b]: Type = default
                dest_m = re.match(r'(\[[^\]]*\])', sp)
                if dest_m and i < len(param_types):
                    pattern_part = dest_m.group(1)
                    rest = sp[dest_m.end():]
                    typed_params.append(f"{pattern_part}: {param_types[i]}{rest}")
                else:
                    typed_params.append(sp)
            elif sp.startswith("..."):
                typed_params.append(sp)
            else:
                typed_params.append(sp)
        new_params = ", ".join(typed_params)
    else:
        new_params = params_str.strip()

    # 织入返回类型
    if ret_type and ret_type not in ("void", "undefined"):
        if "=>" in suffix:
            # 箭头函数: suffix 是 " => {"，返回类型应插入在 => 之前
            new_suffix = f": {ret_type}{suffix}"
        else:
            new_suffix = suffix.replace("{", f": {ret_type} {{")
    else:
        new_suffix = suffix

    replacement = f"{prefix_val}({new_params}){new_suffix}"
    return source[:m.start()] + replacement + source[m.end():]


def _weave_variable(source, name, type_annotation):
    """为变量声明织入类型注解: const name: Type = ...

    返回修改后的源码，若未匹配则返回 None。
    """
    pat = rf'((?:const|var|let)\s+{re.escape(name)})\s*(=\s*)'
    m = re.search(pat, source)
    if not m:
        return None
    repl = f'{m.group(1)}: {type_annotation} {m.group(2)}'
    return source[:m.start()] + repl + source[m.end():]


def weave_file(js_path, exports_info):
    """将导出类型注解织入单个 JS 源码文件。

    Args:
        js_path: JS 源文件路径
        exports_info: 导出列表 [{name, kind, inferred}, ...]
                      注意: 字典会被原地修改 (设置 skip_weave 标记)

    Returns:
        (ts_content, woven_exports): 织入后的 TS 内容, 以及在本文件中织入的导出名列表
    """
    with open(js_path) as f:
        source = f.read()

    original_source = source
    woven_here = []

    for exp in exports_info:
        name = exp["name"]
        kind = exp["kind"]
        inferred = exp.get("inferred", "")

        if kind == "function" and "=>" in inferred:
            result = _weave_signature(source, name, inferred)
            if result is not None:
                source = result
                woven_here.append(name)

        elif kind == "variable" and inferred:
            if inferred in ("unknown", "any", "undefined"):
                continue
            result = _weave_variable(source, name, inferred)
            if result is not None:
                source = result
                woven_here.append(name)

    return source, woven_here


def weave_package(pkg_source_dir, exports_info):
    """对整个包进行类型织入。

    遍历所有 .js 文件，将 exports_info 中的类型织入。每个导出只在首次匹配到
    函数/变量定义的文件中织入，避免在 re-export 的文件中误织入。

    Args:
        pkg_source_dir: 包源码目录
        exports_info: 导出列表 [{name, kind, inferred}, ...]
                      字典会被原地修改

    Returns:
        {relpath: ts_content}  — key 为相对于 pkg_source_dir 的路径 (仍为 .js 后缀)
    """
    woven = {}
    woven_names = set()

    # 收集所有文件，index.js 优先（可能包含 re-export，放后面处理更安全）
    js_files = []
    for root, dirs, files in os.walk(pkg_source_dir):
        dirs[:] = [d for d in dirs if d not in ("node_modules", ".git")]
        for f in files:
            if f.endswith(".js"):
                js_path = os.path.join(root, f)
                rel = os.path.relpath(js_path, pkg_source_dir)
                js_files.append((js_path, rel))

    # 先处理非 index 文件（定义文件），再处理 index 文件（re-export 文件）
    js_files.sort(key=lambda x: (0 if os.path.basename(x[1]) == "index.js" else -1))

    for js_path, rel in js_files:
        # 过滤已全部织入的 exports
        active_exports = [e for e in exports_info if e["name"] not in woven_names]
        if not active_exports:
            ts_content = None
            with open(js_path) as f:
                ts_content = f.read()
            woven[rel] = ts_content
            continue

        ts_content, woven_here = weave_file(js_path, active_exports)
        woven_names.update(woven_here)
        woven[rel] = ts_content

    return woven
