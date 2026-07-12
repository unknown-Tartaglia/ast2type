# 类型织入的已知限制

## 基于导出名称的目标选择

`generate/weave.py` 当前通过本地声明名称和常见 ESM/CommonJS 导出形式，
为每个推导结果选择一个待织入文件。这能避免跨文件时将类型优先写入明显的
私有同名声明，但它仍然是启发式回退，不是精确的声明身份映射。

当前已知限制：

- 只选择文件，不记录文件内的具体声明位置；同一文件存在嵌套或重复同名声明时，
  仍可能修改第一个同名声明。
- `export { local as public }` 和 `export { name } from "./module"` 等 alias/re-export
  形式没有建立公开名称到本地绑定的完整映射。
- `exports = value`、CommonJS 对象属性别名等形式可能被误判或漏判。
- 检测基于源码文本，注释或模板字符串中的导出文本可能产生误判。
- 多个文件导出同名声明时，当前上游会按名称去重，无法稳定区分这些声明。
- Typegraph 中的内部函数也可能有有效推导结果，但当前导出选择路径不会织入它们。

## 后续优化方向

Typegraph 节点已经包含 `file`、`position`、节点 `id` 和 `fullType.id`。后续应：

1. 在 `generate/pipeline_ts.py` 中保留这些声明身份字段，按 `(file, id)` 而不是名称去重。
2. 优先选择 `node.id == fullType.id` 的规范声明节点，过滤同一函数的引用节点。
3. 将文件和声明位置传给织入器，直接修改对应声明，而不是搜索第一个同名文本。
4. 将 typegraph 全声明回填与 `.d.ts` 导出匹配拆成两个明确模式。
5. 使用 TypeScript AST 解析 alias、re-export 和 CommonJS 赋值，避免注释及字符串误判。
6. 补充嵌套同名、alias、re-export、CommonJS 属性别名、注释伪导出和多文件同名测试。
