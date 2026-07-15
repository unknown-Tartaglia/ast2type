# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 常用命令

```bash
# 对测试用例做类型推导（纯约束推断）
./make.sh tests/basic_erase

# 完整流程：擦除 TS 标注 + 生成 AST + 推断
./make.sh tests/basic --prepare

# 对 JS 文件直接做 AST 生成 + 推断（跳过擦除步骤）
./make.sh tests/basic_erase --js --prepare --agent

# 带 Agent LLM 增强的推断
./make.sh tests/basic_erase --agent

# 追踪某个 varId 的类型变化过程
./make.sh tests/basic_erase --trace 108

# JS→TS 迁移：pipeline 方案
./tsify.sh pipeline --source-dir tests/typeweaver --output-dir output_ts

# JS→TS 迁移：纯 LLM 方案（需设置 DEEPSEEK_API_KEY）
./tsify.sh llm --source-dir tests/typeweaver --output-dir output_ts_llm

# 验证生成的 .ts 文件能否通过编译
npx tsc --noEmit --esModuleInterop --moduleResolution bundler --module es2015 --target es6 --lib es2021,dom --skipLibCheck output_ts/pkg/*.ts
```

### 迁移实验评估 (`TypeWeaver/`)

```bash
# 小批量快速迭代（5 包，~50s）：pipeline + tsc + accuracy 一键完成
cd /data/lm/aot/TypeWeaver && ./quick_eval.sh -d test-small

# 强制重跑 pipeline（即使 .ts 已存在）
./quick_eval.sh -d test-small --no-skip

# 仅跑 tsc + accuracy（跳过 pipeline，前提是 .ts 已生成）
./quick_eval.sh -d test-small --tsc-only

# 跳过 auto_fix，直接 tsc，暴露原始推断质量
./quick_eval.sh -d test-small --dry-tsc

# 单包调试
./quick_eval.sh -d test-small -p arrify

# 全量评估（221 包）
./quick_eval.sh -d top1k-typed-nodeps-es6
```

### 实验数据集目录约定

所有路径从一个实验名自动推导：

```
TypeWeaver/data/Pipeline-out/<实验名>/
  conf              ← 包列表（一行一个包名，# 开头为注释）
  source -> ...     ← symlink 指向 original/ 下的 JS 源码
  baseline/         ← 生成的 .ts 文件（pipeline 输出）
  baseline-checked/ ← tsc 编译结果（<pkg>.out = pass, <pkg>.err = fail）
  baseline-typedefs/← 生成的 .d.ts（用于 accuracy 比对）
  accuracy.csv      ← accuracy 汇总
```

**新增实验只需三步**：
```bash
mkdir -p data/Pipeline-out/my-experiment/baseline
ln -s ../../original/top1k-typed-nodeps-es6 data/Pipeline-out/my-experiment/source
echo -e "pkg1\npkg2\npkg3" > data/Pipeline-out/my-experiment/conf
```

### 评估指标

`quick_eval.sh` 输出一张汇总表，同时展示两个维度的指标：

| 指标 | 来源 | 含义 |
|------|------|------|
| **Compile** | tsc --declaration 是否通过 | 编译通过率（目标：尽可能高） |
| **Accuracy** | 生成 .d.ts vs ground truth .d.ts 比对 | 类型正确率（correct/checked，排除 ground truth 为 any 的） |
| **AnyRate** | inferred anys / (anys + checked) | any 率（目标：降低） |

注意：
- compile 失败的包不参与 accuracy 统计（.d.ts 产出不完整）
- accuracy 比对只匹配**单行** `function name(params): RetType` 格式，多行泛型/条件类型暂无法匹配（已知限制）
- 语法错误（TS1xxx）不能被 `@ts-nocheck` 抑制，必须在 weave 阶段解决

## 架构概览

### 核心推断引擎 (TypeScript, `ast2type/`)

基于约束求解的类型推导系统，流程为：**源码 → AST → 事实收集(fact) → 规则应用(rule) → 约束图构建(graph) → 类型求解(solver) → 类型输出**。

- **`fact.ts`** — 类型相关事实定义和存储（赋值、调用、运算、属性访问等），`VarId`/`TypeId` 为全局自增 ID
- **`nType.ts`** — 类型系统。`nType` 为 discriminated union（primitive/literal/array/function/union/object/enum），`tNodeStore` 是全局 TypeId→nType 的注册表，提供类型的创建、合并、序列化
- **`rule.ts`** — 将语言语义编码为类型推导规则，从 Facts 产生 GraphEffect（addEdge/genType/mergeNode等）
- **`graph.ts`** — 类型约束图。节点为 VarId→NodeState，边表示子类型/同类型/ArgToParam/return 等约束关系。核心操作：类型传播、节点合并、冲突检测
- **`solver.ts`** — 工作列表算法的求解器。先 ApplyRules 建图，然后迭代 propagate+extend 直到收敛（最多 1M 次迭代）。支持注入 LLM 推断结果增量求解
- **`strategy.ts`** — 策略接口，`DeterminantStrategy` 实现确定性传播和合并

### JS→TS 迁移管线 (Python, `generate/`)

- **`pipeline_ts.py`** — Pipeline 方案主入口。对每个包：运行 `make.sh --js --prepare --agent` → 从 `output/typegraph.json` 提取导出类型 → 织入 JS 生成 .ts → auto_fix 修复编译错误
- **`weave.py`** — 类型织入引擎。将推断出的函数签名（如 `(a: T1, b: T2) => R`）和变量类型写入 JS 源码生成 .ts，支持正则匹配 function/arrow/const 声明
- **`llm_ts.py`** — LLM 直接方案。对每个 .js 文件调用 DeepSeek API，直接输出带完整类型注解的 .ts 代码
- **`auto_fix.py`** — 自动修复引擎。解析 tsc 错误（TS7006/2345/2322/2339等），按策略优先级（语法修复 → 隐式 any → 类型不匹配 → 兜底 `// @ts-ignore`）迭代修复直到通过或无变化。最终仍失败的加 `// @ts-nocheck`

### 入口脚本

- **`make.sh`** — 单包类型推断入口。自动推导 `_erase_output` 等中间目录路径，组合擦除→AST→推断三阶段
- **`tsify.sh`** — JS→TS 迁移分发入口，路由到 `pipeline_ts.py` 或 `llm_ts.py`
- **`eraseAnnotation.ts`** — 使用 ts-morph 擦除 TypeScript 类型标注，同时生成 `_groundtruth.json` 用于后续评估

### 辅助模块

- **`code2ast.ts`** — AST 生成器，输出 `.ast.json` 和文件索引
- **`statistics.py`** / **`evaluation_stats.py`** — 类型分布和准确率统计，生成 matplotlib 图表
- **`agent/infer.ts`** — LLM Agent 推理引擎。收集 unkinfo（图中无类型的声明盲点）、按文件分组、并发调用 DeepSeek 推断类型、写回 `inferinfo.json` 供 solver 注入

### 测试目录结构 (`tests/`)

每个测试项目遵循约定：`<name>` 为 TS 源码，`<name>_erase` 为擦除后的 JS，`<name>_erase_output` 为推断结果（AST+typegraph）。`make.sh` 自动推导这些路径。

## 当前工作重点

**当前 Goal：在小数据集上，通过设计 Any 率 ↔ 编译通过率的权衡策略，评测「用当前推导出的类型做 JS→TS 迁移」的效果。前提是不让 weave 织入与 auto_fix 修复引入结构性错误，以保证评测干净可信。**

- **评测对象**：推导引擎产出的类型，用于 JS→TS 迁移时的实际表现。
- **方法 / 杠杆**：设计权衡策略——把推导不准 / 错误的类型降级为 `any`，换取 tsc 编译通过，量化「Any 率 ↔ 编译通过率」这条 trade-off 曲线能走多高。
- **前提约束（硬门槛）**：类型只能注入声明位置；weave 织入和 auto_fix 修复**都不得**在使用位置（`${}` 模板插值、函数调用实参、表达式引用）插入类型而制造语法错误（TS1xxx）。否则结构 bug 会污染指标，测不出推导类型的真实迁移效果。
- **载体**：小数据集（如 `test-small`）运行 + 评估，快速迭代。
- **指标**：Compile（编译通过率，主）、AnyRate（代价）、Accuracy（推导质量参考）。

**迭代进展（test-small）**：
- 修复 `auto_fix._fix_implicit_any`：改用 tsc 列号(e.col)精确定位参数声明位置插入 `: any`，不再全行正则替换 → 消除「${x} 被误注解成 ${x: any}」等使用位置结构错误，使用位置误注解 3→0。
- **移除 @ts-nocheck 兜底(作弊)**：auto_fix 步骤3不再整文件加 @ts-nocheck。诚实编译率(真实类型检查)：test-small **Pipeline 4/10**——ML/LLM 方法中最高(它们 1-2/10)，但略低于 tsc 基线(5/10)。此前9/10是 nocheck 灌水的假象。合法手段只有把类型降级为 any。
- 剩余 FAIL：`co` —— tsc 在 `--declaration` 生成 .d.ts 时内部崩溃(Debug Failure @ handleSymbolAccessibilityError)，`--noEmit` 下正常。属 tsc 自身 bug × 评测强制 --declaration 的交互，非我们注入的结构错误，@ts-nocheck 无法抑制。
- **硬门槛闭环验证**：`--dry-tsc --no-skip` 跑纯 weave 产物(无 auto_fix)，使用位置误注解 0 处、Compile 9/10 —— 证明 weave 自身也不产生结构性错误。且当前 tsc 配置未开 --strict/--noImplicitAny，TS7006 不报错，纯 weave 本就编译干净；此前 3 包 FAIL 全由旧 auto_fix 的结构 bug 造成(把能过的包搞挂)。co 在纯 weave 阶段即 crash，与 weave/auto_fix 无关。

- **小批量迭代**：`cd /data/lm/aot/TypeWeaver && ./quick_eval.sh -d test-small`（5 包，~50s）
- **全量评估**：`./quick_eval.sh -d top1k-typed-nodeps-es6`（221 包）
- **实验数据路径**：`/data/lm/aot/TypeWeaver/data/Pipeline-out/<实验名>/`（详见上方"实验数据集目录约定"）
- **本地 tsc 版本**：`npx tsc` 解析到 `node_modules/.bin/tsc`（5.9.3）

关键调参位置：
- `generate/auto_fix.py` 的修复策略 —— 影响 .ts 最终是否通过 `tsc --noEmit`。注意 `@ts-nocheck` 只抑制类型错误（TS2xxx），不抑制语法错误（TS1xxx），因此语法错误必须被修复
- `generate/pipeline_ts.py` 的 `_full_type_to_ts()` —— 控制哪些类型被输出为 `any`
- `generate/weave.py` 的 `_sanitize_ts_type()` —— 清洗畸形类型为 `any`
