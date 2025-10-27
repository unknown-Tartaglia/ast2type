# split_bundle_es6.py
import os
import re
import argparse
from ts_parser import parse_ts

# ------------------- 规则基类 -------------------
class ExportRule:
    """导出规则基类"""
    def match(self, code: str, context) -> bool:
        return False

    def transform(self, code: str, context) -> str:
        return code


# ------------------- 处理 __d 的规则 -------------------
class BundleFunctionES6Rule(ExportRule):
    """处理 React Native bundle 中的 __d 包装函数"""

    def match(self, code, context) -> bool:
        return code.strip().startswith("__d(")

    def transform(self, code, context) -> str:
        # 匹配 __d 包装：__d(function(...) {...}, "filehash", [deps])
        m = re.search(
            r'__d\(\s*\(?\s*function\s*\([^\)]*\)\s*\{([\s\S]*?)\}\s*\)?\s*,\s*"([^"]+)",\s*(\[[^\]]*\])\)',
            code
        )
        if not m:
            return code

        body_code = m.group(1).strip()
        file_hash = m.group(2)
        dep_text = m.group(3)

        # 将 file_hash 存入上下文（可用于文件名）
        context["file_hash"] = file_hash

        # 解析依赖列表
        dependency_map = re.findall(r'["\']([^"\']+)["\']', dep_text)
        context["dependency_map"] = dependency_map

        # 构造 import 语句
        imports = []
        mod_vars = []
        for idx, dep in enumerate(dependency_map):
            var_name = f"mod_{idx}"
            imports.append(f'import {var_name} from "./{dep}.js";')
            mod_vars.append(var_name)

        # 替换 _dependencyMap[n] → 对应 import 变量
        def repl_dep(match):
            idx = int(match.group(1))
            return mod_vars[idx] if idx < len(mod_vars) else match.group(0)

        body_code = re.sub(r'(?:_dependencyMap|_?d)\[(\d+)\]', repl_dep, body_code)


        # 替换 _$$_REQUIRE(mod_n) → mod_n
        def repl_require(match):
            var = match.group(1)
            return var if var in mod_vars else match.group(0)

        body_code = re.sub(r'(?:_\$\$_REQUIRE|_?r)\((mod_\d+)\)', repl_require, body_code)

        # 拼接文件头 + import + 代码体
        header = f"// File: {file_hash}.js\n"
        return header + "\n".join(imports) + "\n\n" + body_code


# ------------------- 处理 exports.<name> 的规则 -------------------
class CommonJSExportToES6Rule(ExportRule):
    """处理 exports.xxx = ... 转换为 ES6 export"""

    def match(self, code, context) -> bool:
        return ("exports." in code) or ("e." in code) or ("_e." in code)

    def transform(self, code, context) -> str:
        def repl_export(match):
            name = match.group(1)
            value = match.group(2).strip()
            if name == "default":
                return f"export default {value};"
            else:
                return f"export const {name} = {value};"

        # 匹配 exports.xxx = ... (允许逗号或分号结束)
        return re.sub(
            r"(?:exports|_?e)\.(\w+)\s*=\s*([^,;]+)[,;]",
            lambda m: repl_export(m),
            code
        )


# ------------------- 处理 module.exports 的规则 -------------------
class ModuleExportsToES6Rule(ExportRule):
    def match(self, code, context) -> bool:
        # 只要出现 module.exports 相关语句就触发
        return bool(re.search(r'\b(?:module|_?m)\.(?:exports|_?e)\b', code))

    def transform(self, code, context) -> str:
        # 专门匹配一整条 module.exports 语句（到分号结束，或者文件末尾）
        def repl_module_exports(match):
            stmt = match.group(1).strip()

            # 按逗号拆分（逗号表达式）
            parts = [p.strip() for p in stmt.split(",")]
            new_lines = []

            for p in parts:
                # module.exports = XXX
                m = re.match(r'^(?:module|_?m)\.(?:exports|_?e)\s*=\s*(.+)$', p)
                if m:
                    new_lines.append(f"export default {m.group(1)};")
                    continue

                # module.exports["default"] = module.exports -> 忽略
                if re.match(r'^(?:module|_?m)\.(?:exports|_?e)\["default"\]\s*=\s*(?:module|_?m)\.(?:exports|_?e)$', p):
                    continue

                # __esModule 标记 -> 忽略
                if "__esModule" in p:
                    continue

                # 其他情况原样保留（防止误删）
                new_lines.append(p)

            return "\n".join(new_lines)

        # 只替换 module.exports 开头的语句
        return re.sub(r'((?:module|_?m)\.(?:exports|_?e)[^;]*)(?:;|$)', repl_module_exports, code)




# ------------------- 所有规则 -------------------
RULES = [
    BundleFunctionES6Rule(),
    CommonJSExportToES6Rule(),
    ModuleExportsToES6Rule(),
]


# ------------------- 应用规则 -------------------
def apply_rules(code: str, context) -> str:
    """依次应用所有规则"""
    for rule in RULES:
        if rule.match(code, context):
            code = rule.transform(code, context)
    return code

# ------------------- 核心拆分逻辑 -------------------
def split_js_file(input_file: str, output_dir: str):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    with open(input_file, 'r', encoding='utf-8') as f:
        code = f.read()
    tree = parse_ts(code)
    root_node = tree.root_node

    for i, statement_node in enumerate(root_node.children):
        statement_code = statement_node.text.decode('utf-8').strip()
        if not statement_code or statement_code == ";":
            continue

        context = {}
        output_code = apply_rules(statement_code, context)

        file_hash = context.get("file_hash", f"stmt{i}")
        output_filename = os.path.join(output_dir, f"{file_hash}.js")
        with open(output_filename, 'w', encoding='utf-8') as out_f:
            out_f.write(output_code)
        print(f"Saved statement {i} to {output_filename}")

# ------------------- CLI -------------------
def main():
    parser = argparse.ArgumentParser(description="Split JS bundle and generate ES6 import/export.")
    parser.add_argument("input_file", help="Path to JS input file")
    parser.add_argument("output_dir", help="Path to output directory")
    args = parser.parse_args()
    split_js_file(args.input_file, args.output_dir)

if __name__ == "__main__":
    main()
