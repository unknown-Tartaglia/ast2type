# CLAUDE.md

本文记录 `ast2type` 的稳定开发约定。数据集、批处理、Accuracy 和实验结果属于相邻的
TypeWeaver 仓库，不应放入本仓库。

## 目录职责

```text
ast2type/                 现有类型图、规则和求解器
agent/                    Agent 候选与 provider 通信
src/inference/            推导引擎的稳定调用边界
src/migration/            迁移、编译和修复的生产实现
src/cli.ts                唯一用户入口
tests/regression/         自包含回归测试
```

`src/migration` 内部按能力划分：

| 文件 | 单一职责 |
|---|---|
| `contracts.ts` | 跨模块数据结构 |
| `files.ts` | 文件发现、安全路径和文本编辑 |
| `typegraph.ts` | 内部类型到 TypeScript 类型的转换 |
| `js.ts` | JavaScript 类型标注写回 |
| `ts.ts` | TypeScript 标注擦除与恢复 |
| `project.ts` | 单项目迁移流程 |
| `compiler.ts` | 唯一编译合同 |
| `repair.ts` | 规则修复与编译反馈 Agent loop |

不要在本仓库新增数据集遍历、并发调度、CSV 汇总或实验 manifest 代码。它们应放在
`TypeWeaver/experiments/ast2type/`，并且只能调用统一 CLI，不能复制迁移规则。

## 核心命令

安装依赖、检查生产源码并运行回归测试：

```bash
npm ci
npm run typecheck
npm test
```

迁移一个 JavaScript 项目：

```bash
npm run migration -- migrate-js <js-project> \
  --out <typescript-output> \
  --work-dir <temporary-inference-directory> \
  --mode std
```

Agent 模式使用公平候选：

```bash
npm run migration -- migrate-js <js-project> \
  --out <typescript-output> \
  --work-dir <temporary-inference-directory> \
  --mode agent --candidate-mode fair \
  --agent-provider openai
```

迁移已有 TypeScript 项目时，入口会依次擦除标注、从擦除源码推导、再回填到原槽位：

```bash
npm run migration -- migrate-ts <ts-project> \
  --out <typescript-output> \
  --work-dir <temporary-inference-directory> \
  --mode std
```

编译与修复：

```bash
npm run migration -- check <typescript-project> --contract uniform
npm run migration -- check <typescript-project> --contract project
npm run migration -- repair <typescript-project> --out <fixed-copy> --strategy rules
npm run migration -- repair <typescript-project> --out <fixed-copy> --strategy rules+agent
```

`tsify.sh` 只为旧调用方保留，参数与 `src/cli.ts` 完全相同。

## 推导模式

- `std` 只使用确定性类型图推导。
- `agent` 将 LLM 候选反馈到图中，再继续求解。
- `fair` 候选与 ground truth 无关，是正式对比的默认模式。
- `gt` 保留历史候选行为，只用于复现实验，结果必须明确标注。
- `--agent-signature-only` 只收集参数和函数返回槽，适合签名 Accuracy 实验。
- `--agent-refine-any` 额外复核会在写回时退化为 `any` 的不透明签名槽；它不读取 ground truth。
- 不支持或无法解析的 ground-truth 类型视为 `unknown`，不得注入图。

OpenAI 使用 `OPENAI_API_KEY`，DeepSeek 使用 `DEEPSEEK_API_KEY`。provider、model 和
base URL 可以通过 CLI 参数或对应环境变量覆盖。

## 不可破坏的合同

### 类型写回

- 只修改声明或签名中的类型位置，不修改调用、实参或其他运行时表达式。
- JavaScript 写回以 typegraph 的文件、源码位置和 canonical id 为身份。
- TypeScript 回填以擦除时记录的 span 为身份；ground truth 类型值不参与 fair 推导。
- 保留默认参数、注释、shebang、指令、UTF-8 内容和原换行风格。
- 无效内部类型降级为 `any`，rest 参数降级为 `any[]`。

### Auto-fix

- 规则修复通过 TypeScript AST 和 type checker 将 diagnostic 定位到声明。
- 规则只替换已有 TypeNode 或插入安全的声明类型，不写 `@ts-ignore`、cast 或运行时代码。
- 无法唯一定位时跳过；每轮修改后必须用同一编译合同重检。
- Agent 编辑使用唯一原文锚点，逐条编译，只有诊断数单调下降且不新增语法/环境错误才保留。

### 编译

- `uniform` 是 TypeWeaver 公平比较合同，执行 declaration emit 和 `noEmitOnError`。
- `project` 使用项目自己的 `tsconfig`，用于补齐依赖后的真实项目实验。
- 修复和最终评测必须调用 `src/migration/compiler.ts` 的同一实现。
- 工具错误、空输入和缺失输入不能计为方法编译失败或编译通过。
- 编译失败不得留下旧的或部分 declaration 输出。

### Raw 与 Fixed

- `migrate-js` / `migrate-ts` 输出是 raw。
- fixed 必须由 `repair --out` 从 raw 的副本生成。
- 正式实验必须同时保留 raw 和 fixed，并报告包级通过率与 diagnostic 总数。

## 跨仓库实验

TypeWeaver 的正式入口是：

```bash
python3 experiments/ast2type/run.py \
  --source-dir <dataset> \
  --output-dir <experiment-output> \
  --modes std,agent
```

两个仓库分别提交。实验记录应保存双方 commit、配置、数据集和编译器版本；不要用未版本化
的历史 CSV 冒充当前复检结果。

## 测试与 Git

- 修改生产代码后运行 `npm run typecheck` 和 `npm test`。
- 对解析、UTF-16 偏移、路径边界和 AST 定位增加行为测试。
- 只在非显然逻辑前写简洁注释，不写逐行翻译式注释。
- 不提交 `output/`、`*_erase`、`*_output`、declaration、baseline、日志或模型响应。
- dirty worktree 中精确暂存路径，保留用户和实验数据的无关改动。
