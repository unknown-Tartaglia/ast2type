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


# ==================== 类型字符串清洗 ====================

def _sanitize_ts_type(ts_type):
    """清洗单个 TypeScript 类型字符串，确保语法合法。

    Returns:
        合法的类型字符串，若无法修复则返回 "any"
    """
    if not ts_type or not isinstance(ts_type, str):
        return "any"
    ts_type = ts_type.strip()
    if not ts_type:
        return "any"
    if re.search(r'[:;]\s*$', ts_type):
        return "any"
    # 匹配匿名对象类型 obj_数字
    if re.match(r'^obj_\d+$', ts_type):
        return "any"
    # constructor 类型: "new (params) : RetType" 或 "new (params) => RetType"
    if ts_type.startswith("new ") or re.match(r'^new\s*\(', ts_type):
        return "any"
    # 函数返回类型语法 "): Type" — 不是合法 TS 类型
    if re.search(r'\)\s*:\s+\w', ts_type):
        return "any"
    # 非法字符检测
    if re.search(r'[^\w\[\]\(\)<>\s\'\"`,\.\|\&\-\?\:;=/\^]', ts_type):
        return "any"
    # 括号不匹配 (跳过 => 中的 >, 它不是闭合尖括号)
    depth = 0
    prev = ''
    for ch in ts_type:
        if ch in '([{<':
            depth += 1
        elif ch == '>' and prev == '=':
            pass  # => 中的 > 不算
        elif ch in ')]}>':
            depth -= 1
        if depth < 0:
            return "any"
        prev = ch
    if depth != 0:
        return "any"
    return ts_type


def _split_function_arrow(inferred):
    """Split a function type at its outermost arrow."""
    depth = 0
    quote = None
    escaped = False
    for index, char in enumerate(inferred):
        if quote:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in "'\"`":
            quote = char
        elif char in "([{<":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == ">" and (index == 0 or inferred[index - 1] != "="):
            depth = max(0, depth - 1)
        elif char == "=" and depth == 0 and inferred[index:index + 2] == "=>":
            return inferred[:index], inferred[index + 2:]
    return None


def _sanitize_inferred(inferred):
    """清洗完整的 inferred 类型签名 '(a: T1, b: T2) => R'。

    Returns:
        清洗后的签名，确保所有类型子串合法
    """
    if not inferred or "=>" not in inferred:
        return inferred
    split = _split_function_arrow(inferred)
    if split is None:
        return inferred
    sig, ret = split
    sig = sig.strip()
    ret = ret.strip()

    # 清洗返回类型
    ret = _sanitize_ts_type(ret)
    if ret == "PromiseConstructor":
        ret = "Promise<any>"

    if sig.startswith("(") and sig.endswith(")"):
        inner = sig[1:-1].strip()
    else:
        inner = sig

    if not inner:
        return f"() => {ret}"

    # 按逗号分割参数列表（忽略嵌套括号）
    params = _split_params(inner)
    cleaned = []
    for p in params:
        p = p.strip()
        if ":" in p:
            name, _, ptype = p.partition(":")
            name = name.strip()
            ptype = _sanitize_ts_type(ptype.strip())
            if not name:
                cleaned.append(f"arg: {ptype}")
            else:
                cleaned.append(f"{name}: {ptype}")
        elif p.startswith("..."):
            cleaned.append(p)  # rest params
        else:
            if p:
                cleaned.append(f"{p}: any")
    return f"({', '.join(cleaned)}) => {ret}"


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

def _split_params(params_str):
    """按逗号分割参数列表，忽略嵌套结构和字符串内的逗号。"""
    parts = []
    depth = 0
    current = []
    quote = None
    escaped = False
    for ch in params_str:
        if quote:
            current.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == quote:
                quote = None
            continue
        if ch in "'\"`":
            quote = ch
        elif ch in "{[(<":
            depth += 1
        elif ch in "}])>":
            depth = max(0, depth - 1)
        if ch == "," and depth == 0:
            parts.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    if current:
        parts.append("".join(current).strip())
    return [p for p in parts if p]


def _parse_inferred_params(inferred):
    """从 '(a: T1, b: T2) => R' 或 '() => R' 提取参数类型列表和返回类型。"""
    if "=>" not in inferred:
        return [], inferred.strip()
    split = _split_function_arrow(inferred)
    if split is None:
        return [], "any"
    sig, ret = split
    sig = sig.strip()
    ret = ret.strip()
    # 清洗返回类型
    ret = _sanitize_ts_type(ret)
    if ret == "PromiseConstructor":
        ret = "Promise<any>"
    if sig.startswith("(") and sig.endswith(")"):
        sig = sig[1:-1]
    param_types = []
    if sig.strip():
        for p in _split_params(sig):
            p = p.strip()
            if ":" in p:
                ptype = p.split(":", 1)[1].strip()
                ptype = _sanitize_ts_type(ptype)
                if not ptype:
                    ptype = "any"
                param_types.append(ptype)
            elif p == "..." or p.startswith("..."):
                param_types.append("any[]")
            else:
                param_types.append("any")
    return param_types, ret


# ==================== 类型织入 ====================

def _find_matching_delimiter(source, open_index, open_char="(", close_char=")"):
    """Return the matching delimiter index while ignoring strings and comments."""
    if open_index >= len(source) or source[open_index] != open_char:
        return None
    depth = 0
    quote = None
    escaped = False
    line_comment = False
    block_comment = False
    index = open_index
    while index < len(source):
        char = source[index]
        next_char = source[index + 1] if index + 1 < len(source) else ""
        if line_comment:
            if char == "\n":
                line_comment = False
        elif block_comment:
            if char == "*" and next_char == "/":
                block_comment = False
                index += 1
        elif quote:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
        elif char == "/" and next_char == "/":
            line_comment = True
            index += 1
        elif char == "/" and next_char == "*":
            block_comment = True
            index += 1
        elif char in "'\"`":
            quote = char
        elif char == open_char:
            depth += 1
        elif char == close_char:
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return None


def _weave_signature(source, func_name, inferred):
    """在源码中为指定函数织入参数类型和返回类型。

    返回修改后的源码。若未找到匹配则返回 None。
    """
    param_types, ret_type = _parse_inferred_params(inferred)

    escaped_name = re.escape(func_name)
    declaration = re.search(
        rf'\b(?:async\s+)?function\s+{escaped_name}\s*\(', source
    )
    arrow = False
    if declaration:
        start = declaration.start()
        open_index = declaration.end() - 1
        close_index = _find_matching_delimiter(source, open_index)
        if close_index is None:
            return None
        suffix_match = re.match(r'\s*\{', source[close_index + 1:])
        if not suffix_match:
            return None
        end = close_index + 1 + suffix_match.end()
    else:
        declaration = re.search(
            rf'\b(?:const|var|let)\s+{escaped_name}\s*=\s*(?:async\s*)?\(',
            source,
        )
        arrow = True
        if declaration:
            start = declaration.start()
            open_index = declaration.end() - 1
            close_index = _find_matching_delimiter(source, open_index)
            if close_index is None:
                return None
            suffix_match = re.match(r'\s*=>\s*(?:\{)?', source[close_index + 1:])
            if not suffix_match:
                return None
            end = close_index + 1 + suffix_match.end()
        else:
            bare_arrow = re.search(
                rf'\b(?:const|var|let)\s+{escaped_name}\s*=\s*(?:async\s+)?'
                r'([A-Za-z_$][\w$]*)(\s*=>\s*(?:\{)?)',
                source,
            )
            if not bare_arrow:
                return None
            start = bare_arrow.start()
            open_index = bare_arrow.start(1)
            close_index = bare_arrow.end(1)
            end = bare_arrow.end()
            params_str = bare_arrow.group(1)
            prefix_val = source[start:open_index]
            suffix = bare_arrow.group(2)

    if declaration:
        prefix_val = source[start:open_index]
        params_str = source[open_index + 1:close_index]
        suffix = source[close_index + 1:end]

    # 织入参数类型
    if param_types and params_str.strip():
        source_params = _split_params(params_str)
        typed_params = []
        for i, sp in enumerate(source_params):
            if not sp:
                typed_params.append(sp)
                continue
            if sp.startswith("..."):
                rest_m = re.match(r'\.\.\.([A-Za-z_$][\w$]*)', sp)
                if rest_m:
                    pname = rest_m.group(1)
                    rest = sp[rest_m.end():]
                    ptype = param_types[i] if i < len(param_types) else "any[]"
                    if not ptype.endswith("[]") and not ptype.startswith("Array<"):
                        ptype = "any[]"
                    typed_params.append(f"...{pname}: {ptype}{rest}")
                else:
                    typed_params.append(sp)
                continue
            name_m = re.match(r'([A-Za-z_$][\w$]*)', sp)
            if name_m and i < len(param_types):
                pname = name_m.group(1)
                rest = sp[name_m.end():]
                ptype = param_types[i] if param_types[i] else "any"
                # 确保 ptype 不是空字符串
                if not ptype.strip():
                    ptype = "any"
                typed_params.append(f"{pname}: {ptype}{rest}")
            elif name_m:
                # 参数数量不匹配, 加 any
                pname = name_m.group(1)
                rest = sp[name_m.end():]
                typed_params.append(f"{pname}: any{rest}")
            elif sp.startswith("{"):
                dest_m = re.match(r'(\{[^}]*\})', sp)
                if dest_m and i < len(param_types):
                    pattern_part = dest_m.group(1)
                    rest = sp[dest_m.end():]
                    ptype = param_types[i] if param_types[i] else "any"
                    if not ptype.strip():
                        ptype = "any"
                    typed_params.append(f"{pattern_part}: {ptype}{rest}")
                else:
                    typed_params.append(sp)
            elif sp.startswith("["):
                dest_m = re.match(r'(\[[^\]]*\])', sp)
                if dest_m and i < len(param_types):
                    pattern_part = dest_m.group(1)
                    rest = sp[dest_m.end():]
                    ptype = param_types[i] if param_types[i] else "any"
                    if not ptype.strip():
                        ptype = "any"
                    typed_params.append(f"{pattern_part}: {ptype}{rest}")
                else:
                    typed_params.append(sp)
            else:
                typed_params.append(sp)
        new_params = ", ".join(typed_params)
        # 清理空类型注解: ": )" → ")", ": ," → ",", ": }" → "}"
        new_params = re.sub(r':\s*(?=[,)}\]])', '', new_params)
    else:
        new_params = params_str.strip()

    # 织入返回类型
    ret_type_clean = ret_type.strip() if ret_type else ""
    if (
        re.match(r'^[A-Za-z_$][\w$]*$', ret_type_clean)
        and re.search(rf'\bfunction\s+{re.escape(ret_type_clean)}\s*\(', source)
    ):
        # A JavaScript constructor function is a runtime value, not a declared
        # TypeScript type. Let TypeScript infer its structural instance shape.
        ret_type_clean = "any"
    if ret_type_clean and ret_type_clean not in ("void", "undefined", "any"):
        if arrow:
            # 箭头函数: 在 => 前插入返回类型
            new_suffix = f": {ret_type_clean}{suffix}"
        else:
            new_suffix = f": {ret_type_clean} {suffix.lstrip()}"
    else:
        new_suffix = suffix

    replacement = f"{prefix_val}({new_params}){new_suffix}"
    return source[:start] + replacement + source[end:]


def _weave_variable(source, name, type_annotation):
    """为变量声明织入类型注解: const name: Type = ...

    返回修改后的源码，若未匹配则返回 None。
    """
    # 清洗类型注解
    type_annotation = _sanitize_ts_type(type_annotation)
    if type_annotation in ("unknown", "any", "undefined"):
        return None  # 跳过 any/unknown，不添加无效注解

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

    woven_here = []

    for exp in exports_info:
        name = exp["name"]
        kind = exp["kind"]
        inferred = exp.get("inferred", "")

        # 清洗 infered 签名
        if "=>" in inferred:
            inferred = _sanitize_inferred(inferred)

        if kind == "function" and "=>" in inferred:
            result = _weave_signature(source, name, inferred)
            if result is not None:
                source = result
                woven_here.append(name)

        elif kind == "variable" and inferred:
            result = _weave_variable(source, name, inferred)
            if result is not None:
                source = result
                woven_here.append(name)

    return source, woven_here


def _has_local_definition(source, export_info):
    """Return whether weave_file can target this symbol in the source."""
    name = re.escape(export_info["name"])
    if export_info["kind"] == "function":
        patterns = (
            rf'\bfunction\s+{name}\s*\(',
            rf'\b(?:const|var|let)\s+{name}\s*=\s*(?:async\s*)?\(',
            rf'\b(?:const|var|let)\s+{name}\s*=\s*(?:async\s+)?\w+\s*=>',
        )
    else:
        patterns = (rf'\b(?:const|var|let)\s+{name}\b',)
    return any(re.search(pattern, source) for pattern in patterns)


def _has_explicit_export(source, name):
    """Recognize local ES module and CommonJS export forms."""
    escaped = re.escape(name)
    patterns = (
        rf'^\s*export\s+(?:default\s+)?function\s+{escaped}\b',
        rf'^\s*export\s+(?:const|var|let)\s+{escaped}\b',
        rf'^\s*export\s+default\s+{escaped}\b',
        rf'^\s*export\s*\{{[^}}]*\b{escaped}\b[^}}]*\}}',
        rf'^\s*(?:module\.)?exports(?:\s*\.\s*\w+|\s*\[\s*[\'\"]\w+[\'\"]\s*\])?\s*=\s*{escaped}\b',
        rf'^\s*module\.exports\s*=\s*function\s+{escaped}\b',
        rf'^\s*module\.exports\s*=\s*\{{[^}}]*(?:\b{escaped}\b\s*:)?\s*{escaped}\b[^}}]*\}}',
    )
    if any(re.search(pattern, source, re.MULTILINE) for pattern in patterns):
        return True

    exported_roots = set(re.findall(
        r'^\s*(?:export\s+default|module\.exports\s*=)\s*([A-Za-z_$][\w$]*)\b',
        source,
        re.MULTILINE,
    ))
    return any(re.search(
        rf'^\s*{re.escape(root)}\s*\.\s*[A-Za-z_$][\w$]*\s*=\s*{escaped}\b',
        source,
        re.MULTILINE,
    ) for root in exported_roots)


def _weave_candidate_score(source, export_info):
    if not _has_local_definition(source, export_info):
        return 0
    if _has_explicit_export(source, export_info["name"]):
        return 2
    return 0


def _inject_class_fields(source):
    """Declare fields assigned through ``this`` so migrated JS is valid TS."""
    insertions = []
    for match in re.finditer(r'\bclass\s+[A-Za-z_$][\w$]*(?:\s+extends\s+[^\{]+)?\s*\{', source):
        open_index = match.end() - 1
        close_index = _find_matching_delimiter(source, open_index, "{", "}")
        if close_index is None:
            continue
        body = source[open_index + 1:close_index]
        assigned = set(re.findall(r'\bthis\.([A-Za-z_$][\w$]*)\s*=', body))
        if not assigned:
            continue
        declared = set(re.findall(
            r'^\s*(?:declare\s+|public\s+|private\s+|protected\s+|readonly\s+|static\s+)*'
            r'([A-Za-z_$][\w$]*)\s*(?:[!?]\s*)?(?::|=|;)',
            body,
            re.MULTILINE,
        ))
        missing = sorted(assigned - declared)
        if not missing:
            continue
        first_line = re.search(r'\n([ \t]+)\S', body)
        indent = first_line.group(1) if first_line else "  "
        fields = "".join(f"\n{indent}{name}: any;" for name in missing)
        insertions.append((open_index + 1, fields))

    for index, fields in reversed(insertions):
        source = source[:index] + fields + source[index:]
    return source


def _normalize_default_export_assignments(source):
    """Split assignment expressions out of default exports for stable .d.ts emit."""
    pattern = re.compile(
        r'^(\s*)export\s+default\s+'
        r'(?P<assignment>(?P<name>[A-Za-z_$][\w$]*)\[[\'\"]default[\'\"]\]\s*=\s*'
        r'(?P=name)\.[A-Za-z_$][\w$]*\s*=\s*(?P=name))\s*;',
        re.MULTILINE,
    )

    def replace(match):
        indent = match.group(1)
        return (
            f"{indent}{match.group('assignment')};\n"
            f"{indent}export default {match.group('name')};"
        )

    return pattern.sub(replace, source)


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

    # 收集所有文件，index.js 优先（可能包含 re-export，放后面处理更安全）
    js_files = []
    for root, dirs, files in os.walk(pkg_source_dir):
        dirs[:] = [d for d in dirs if d not in ("node_modules", ".git")]
        for f in files:
            if f.endswith((".js", ".mjs")):
                js_path = os.path.join(root, f)
                rel = os.path.relpath(js_path, pkg_source_dir)
                js_files.append((js_path, rel))

    # 先处理非 index 文件（定义文件），再处理 index 文件（re-export 文件）
    js_files.sort(key=lambda x: (0 if os.path.basename(x[1]) == "index.js" else -1))

    sources = {}
    for js_path, rel in js_files:
        with open(js_path) as f:
            sources[rel] = f.read()

    # This is a name-based fallback until typegraph source positions are
    # preserved end to end. See docs/weave-known-limitations.md.
    # Internal names from the typegraph are intentionally left unannotated.
    exports_by_file = {rel: [] for _, rel in js_files}
    for export_info in exports_info:
        candidates = []
        for order, (js_path, rel) in enumerate(js_files):
            score = _weave_candidate_score(sources[rel], export_info)
            if score:
                candidates.append((score, -order, js_path, rel))
        if candidates:
            _, _, _, selected_rel = max(candidates)
            exports_by_file[selected_rel].append(export_info)

    for js_path, rel in js_files:
        selected_exports = exports_by_file[rel]
        if selected_exports:
            ts_content, _ = weave_file(js_path, selected_exports)
            woven[rel] = _inject_class_fields(_normalize_default_export_assignments(ts_content))
        else:
            woven[rel] = _inject_class_fields(
                _normalize_default_export_assignments(sources[rel])
            )

    return woven
