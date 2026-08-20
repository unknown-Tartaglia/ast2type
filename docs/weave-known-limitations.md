# 类型写回的已知限制

当前 JavaScript 写回已不再按名称搜索声明，而是使用 typegraph 中的文件、源码位置以及
`node.id == fullType.id` 的 canonical 节点定位 TypeScript AST。

仍需注意以下边界：

- bundle 生成的 hash/虚拟模块名可能没有对应真实源码文件，此类目标会明确记为 skipped；
- typegraph 位置与输入源码版本不一致时不会猜测同名声明；
- 同一位置对应多个函数节点时视为歧义并跳过；
- 当前只恢复函数参数和返回类型，变量、类成员等更多声明位置仍需单独扩展；
- class field、特殊 default export 和 Node 全局声明属于 JS 到 TS 兼容处理，会在报告中
  单独计数。

扩展定位范围时应在 `src/migration/js.ts` 或 `src/migration/ts.ts` 中实现，并补充源码位置、
UTF-16 和运行时文本保持测试，不能重新引入基于正则或名称的全局替换。
