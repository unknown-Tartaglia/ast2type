# CLAUDE.md

本文记录 `ast2type` 稳定的开发与评测约定。阶段性实验结果应保存在 TypeWeaver
的运行 manifest 中，不要写入本文。

## 仓库职责

`ast2type` 负责：

- JavaScript 与 TypeScript 类型推导；
- Agent 候选生成与反馈注入；
- JavaScript 到 TypeScript、擦除后 TypeScript 到 TypeScript 的迁移；
- 推导类型织入与保守的 auto-fix；
- 统一的 TypeScript 编译合同；
- 聚焦回归测试与仓库完整回归测试。

相邻的 TypeWeaver 是独立维护的 fork，负责数据集、实验编排、官方 Accuracy
适配、运行 manifest 和跨方法结果汇总。不要把 TypeWeaver 数据或实验生成物移入本仓库。

## 核心命令

在仓库根目录安装依赖并运行已跟踪的完整回归测试：

```bash
npm ci
npm test
```

修改具体子系统时，可先运行对应的聚焦测试：

```bash
python3 -m unittest tests.regression.test_agent_candidate_modes -v
python3 -m unittest tests.regression.test_agent_providers -v
python3 -m unittest tests.regression.test_erased_ts_migration -v
python3 -m unittest tests.regression.test_tsc_check -v
python3 -m unittest tests.regression.test_auto_fix -v
```

### 本地夹具推导

对已跟踪的 TypeScript 夹具运行标准推导：

```bash
./make.sh tests/ts/personal --prepare
```

Agent 推导默认使用 `fair` 候选：

```bash
./make.sh tests/ts/personal --prepare --agent --agent-candidate-mode fair
```

Agent API 默认使用 DeepSeek。直接调用 OpenAI Responses API 时设置
`OPENAI_API_KEY` 并选择 `openai` provider：

```bash
OPENAI_API_KEY='your-key' ./make.sh tests/ts/personal --prepare --agent \
  --agent-provider openai
```

OpenAI 默认模型为 `gpt-4.1-mini`。可通过 `--agent-model` 和
`--agent-base-url` 覆盖；对应的环境变量为 `AGENT_MODEL`、
`OPENAI_MODEL`、`AGENT_BASE_URL` 和 `OPENAI_BASE_URL`。API key 只从
`--api-key` 或当前 provider 对应的 `OPENAI_API_KEY`/`DEEPSEEK_API_KEY` 读取。

旧版/兼容候选集使用 `gt`：

```bash
./make.sh tests/ts/personal --prepare --agent --agent-candidate-mode gt
```

上述针对 TypeScript 夹具的 `make.sh` 命令会自动把生成的 `_groundtruth.json`
通过 `-g` 传回推导器。它们适合调试图、候选集和兼容行为，但不是 GT-independent
的正式评测命令。正式的 fair TypeScript 评测应使用下文的
`pipeline_erased_ts.py`。

使用 `--trace <varId>` 跟踪图传播，使用 `-f <feedback.json>` 重放外部反馈。
Agent 反馈会注入图中并继续求解直至收敛，而不只是迁移时临时写入标注。

### JavaScript 到 Raw TypeScript

`pipeline_ts.py` 只生成 raw 织入结果，不执行 auto-fix：

```bash
python3 generate/pipeline_ts.py \
  --source-dir <javascript-packages> \
  --output-dir <raw-typescript> \
  --packages package-a,package-b
```

等价的分发入口是 `./tsify.sh pipeline ...`。该 pipeline 依次执行 JavaScript-only
AST 准备、Agent 推导、typegraph 提取、类型织入、Node 全局声明注入，并隔离单包失败。

### 擦除后 TypeScript 迁移

评测已有 TypeScript 项目时使用擦除迁移 pipeline。它会擦除标注、从擦除后的源码推导，
再把推导标注恢复到擦除后的 TypeScript 中：

```bash
python3 generate/pipeline_erased_ts.py \
  --projects-root tests/ts \
  --output-root /tmp/ast2type-erased-run \
  --packages personal,mapcn \
  --agent
```

省略 `--agent` 即使用标准推导。只有通过 `--reuse-inference-root` 才允许复用推导；
复用前必须验证擦除源码逐字节一致，并验证 standard/Agent 模式以及 Agent provider、
model、base URL 的 manifest 一致。

### 统一 TypeScript 编译

所有正式编译检查和 auto-fix 迭代都必须使用 `generate/tsc_check.py`：

```bash
python3 generate/tsc_check.py config --field version
python3 generate/tsc_check.py check \
  --declaration-dir /tmp/ast2type-declarations \
  --diagnostics-file /tmp/ast2type-diagnostics.txt \
  --status-file /tmp/ast2type-status.txt \
  path/to/source.ts
```

不能用 `tsc --noEmit` 代替正式检查。统一合同会执行 declaration emit 和
`--noEmitOnError`，并把结果分类为 `PASS`、`TYPE_ERROR` 或 `TOOL_ERROR`。

### 保守 Auto-Fix

Auto-fix 与 raw 生成必须分开执行。除非显式传入 `--in-place`，批处理入口默认采用
copy-on-write：

```bash
python3 generate/run_auto_fix_all.py \
  --baseline-dir <raw-package-root> \
  --output-dir <fixed-package-root> \
  --results <run-manifest.json>
```

输出目录和结果文件不能已经存在，也不能与 baseline 或包输出目录重叠。

## 架构

类型推导主流程为：

```text
源码 -> AST -> 事实 -> 规则 -> 约束图 -> 求解器 -> 类型输出
```

核心模块：

- `ast2type/fact.ts`：语言事实与事实存储；
- `ast2type/rule.ts`：语义规则与图效果；
- `ast2type/graph.ts`：约束图与类型传播；
- `ast2type/solver.ts`：工作列表求解与反馈再注入；
- `ast2type/nType.ts`：内部类型表示与序列化；
- `ast2type/strategy.ts`：确定性/概率化策略边界；
- `agent/infer.ts`：LLM Agent 候选推导；
- `generate/weave.py`：推导结果声明织入；
- `generate/weave_erased_ts.py`：基于 span 的擦除后 TypeScript 恢复；
- `generate/auto_fix.py` 与 `generate/locate_auto_fix.js`：基于 AST 定位的类型降级；
- `generate/tsc_check.py`：编译与 declaration emit 合同。

## 不可破坏的合同

### Fair 与 Ground-Truth 候选模式

- `fair` 是默认模式，也是 GT-independent 正式结果唯一允许使用的候选模式。
- `fair` 只保证 Agent 候选发现与 ground truth 无关；只有整次运行没有额外使用
  `-g` 注入图约束时，完整结果才是 GT-independent。
- `gt` 保留历史 graph 候选行为，可能暴露带 ground-truth 标注的图位置，必须明确标为
  `gt`。
- 不能比较未标注或混合了 `fair`、`gt` 的结果。
- 不支持或无法解析的 ground-truth 类型属于 `unknown`，不得作为约束注入。

擦除后 TypeScript 迁移可以使用 ground-truth span 元数据定位原标注槽位，但 fair
推导不得使用 ground-truth 类型值。

### 类型织入

- 类型只能写入声明或签名位置。
- 不得改写函数调用、实参、模板插值、属性使用或其他运行时表达式。
- 必须保留默认参数表达式、注释、shebang、指令，以及 UTF-8 内容和换行风格。
- 必须保留原始源码和 raw 织入结果，以便比较。

修改基于名称的导出目标选择前，先阅读 `docs/weave-known-limitations.md`。

### Auto-Fix

- 必须通过 TypeScript AST/type checker，把 diagnostic 解析到可编辑声明。
- 只允许把已有声明 `TypeNode` 替换为 `any`，或在需要时插入安全的参数、变量、
  属性类型标注。
- 禁止使用 `@ts-ignore`、`@ts-nocheck`、表达式 cast 或使用位置改写。
- 无法找到唯一安全声明目标时必须跳过。
- for-in/for-of 中不安全的声明标注必须跳过。
- 必须正确处理 UTF-16 diagnostic 偏移并保留 CRLF。

当前安全支持的 diagnostic 为 TS7006、TS2322、TS2339、TS2358、TS2538 和
TS2571。扩展错误码前必须增加行为测试，证明运行时文本没有改变。

### 编译合同

- 确定性地发现 `.ts`、`.tsx`、`.mts` 和 `.cts` 根文件。
- 排除 `.d.ts`、`.d.mts`、`.d.cts`、`.ets`、`node_modules` 和 `.git`。
- Auto-fix 与最终评测必须调用同一份共享合同。
- `TOOL_ERROR` 不能计作方法自身的类型错误。
- 调用方必须单独报告空包，不能把空输入当作有意义的编译通过。
- 编译失败后不能留下旧的或部分生成的 declaration 输出。

### Raw 与 Fixed 结果

- `pipeline_ts.py` 的输出是 `raw`。
- `fixed` 必须从 `raw` 的副本通过独立 auto-fix 入口生成。
- 正式比较中禁止修改规范 raw baseline。
- Run manifest 必须记录编译器版本、参数、输入/输出指纹、状态、diagnostic/edit 数量、
  修改路径和耗时。
- 当前结果不能以未版本化的历史 CSV 为来源。

所有 TypeWeaver runner 都必须遵守该拆分。`pipeline_ts.py` 不存在
`--no-auto-fix` 选项，因为它本身从不执行 auto-fix。

## 评测结果报告

每次比较必须注明：

- 数据集或项目集合；
- 推导模式：`std` 或 `agent`；
- Agent 候选模式：`fair` 或 `gt`；
- 结果变体：`raw`、`fixed` 或 `groundtruth`；
- 编译合同与编译器版本；
- 包或文件的分母。

类型推导表必须拆分 `Wrong` 和 `Undetermined`。需要同时展示两种正确率时，必须明确写出
公式：

- 已判定正确率：`Correct / (Correct + Wrong)`；
- 包含未定项的正确率：`Correct / (Correct + Wrong + Undetermined)`。

同时分别报告 `Missing`、`Any`、`Unknown` 和 `Ignored`。解释 ground truth 或推导结果
无法编译的原因时，不能隐藏缺失模块 diagnostic。

编译结果表必须同时给出包级通过率和 diagnostic 总数，并拆分 `TYPE_ERROR`、
`TOOL_ERROR`、缺失输入和空输入。与 TypeWeaver 比较 Accuracy 时必须复用其官方兼容
语义，即使该比较器有意保持粗粒度。

## 跨仓库实验

TypeWeaver fork 应通过 `AST2TYPE_ROOT` 定位本仓库，只把相邻目录作为便利的默认值。
TypeWeaver 负责 `quick_eval.sh`、官方 Accuracy 适配器和实验 manifest。

正式 manifest 必须记录两个仓库各自的 commit、branch、dirty 状态和实现指纹。
跨仓库改动应分别提交，并在实验记录中引用配对的 commit hash。

## 测试与 Git 约定

- 开发时运行聚焦测试，每次提交前运行 `npm test`。
- 可能依赖未跟踪实验文件的改动，必须把暂存内容导出到干净临时目录中测试。
- 对非显然的解析、偏移、图算法或文件系统安全逻辑添加简洁注释。
- 不要提交新生成的 `output/`、`*_erase`、`*_output`、declaration、baseline、
  checked result、run log 或实验结果目录；只有被已跟踪测试明确使用并经过评审的固定
  回归夹具可以例外。
- 在来源、版本、许可证和最小测试用途得到说明前，不要提交 `tests/typeweaver/` 中的
  外部包夹具。
- 在 dirty worktree 中必须精确暂存路径，并保留无关的用户改动或数据改动。

已跟踪的回归测试必须自包含，不能依赖生成的实验输出或未跟踪的相邻 TypeWeaver
checkout。
