# TypeScript 类型提取工具

快速把 TS 源码转成结构化类型 JSON

## 依赖安装

```bash
npm install
# 或
pnpm install

# 如果没有 ts-node
npm install -g ts-node typescript
```

## 使用方法

1. **源码 → AST + import_map**
   ```bash
   ts-node code2ast.ts -i inputDir
   # 输出到 inputDir_output/
   ```

2. **AST → 类型 JSON**
   ```bash
   ts-node ast2type.ts -i inputDir_output
   # 输出到 ./output/typeinfo/xxx.json
   ```
