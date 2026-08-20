# TypeWeaver 最新评测结果

本文记录 `top1k-typed-nodeps-es6` 数据集上的最新结果。数据集包含 245 个包，
编译器统一为 TypeScript 5.9.3。

当前统一复检表不列旧 AST Pipeline 和 LegacyPipeline：旧 Pipeline 的修复范围不只包含
类型降级，LegacyPipeline 还包含 `@ts-nocheck`，不适合和当前方法放在同一张正式表中。
LambdaNet 的现有产物没有可供统一编译器复检的 TS 根文件，因此当前结果标为不可复检；
它与其他 TypeWeaver 方法的历史结果在 2.1 节单独列出。

## 1. 指标定义

| 指标 | 定义 |
|---|---|
| TypeCheck | 编译通过的包数 / 该方法成功生成结果的包数 |
| 通过率 | TypeCheck 的百分比 |
| Accuracy | 正确类型数 / 可比较的非 `any` 类型数 |
| AnyRate | 推导为 `any` 的数量 /（`any` 数量 + 可比较类型数） |
| 覆盖 | 该方法成功生成结果的包数 / 当前数据集包数 |

Accuracy 和 AnyRate 只在每种方法自身编译通过的包上统计。TypeCheck 按整个包判定：
包内任意一个源文件仍有编译错误，整个包都算失败。

## 2. 全量数据结果

全量结果使用全部 245 个包。TypeCheck 分母仍按各方法自身成功生成的包数计算，
缺失情况通过“覆盖”单独展示。

| 方案 | TypeCheck | 通过率 | Accuracy | Acc% | AnyRate | any% | 覆盖 |
|---|---:|---:|---:|---:|---:|---:|---:|
| TS 推断基线（tsc） | 108/241 | 44.8% | 36/116 | 31.0% | 61/177 | 34.5% | 241/245 |
| DeepTyper | 54/226 | 23.9% | 21/42 | 50.0% | 18/60 | 30.0% | 226/245 |
| LambdaNet | 不可复检 | - | - | - | - | - | 0/245 |
| InCoder | 55/245 | 22.4% | 12/23 | 52.2% | 7/30 | 23.3% | 245/245 |
| SantaCoder | 76/245 | 31.0% | 39/71 | 54.9% | 26/97 | 26.8% | 245/245 |
| 纯 LLM | 96/229 | 41.9% | 53/73 | 72.6% | 4/77 | 5.2% | 229/245 |
| AST 标准，无 fix | 95/245 | 38.8% | 14/89 | 15.7% | 67/156 | 42.9% | 245/245 |
| AST 标准，Auto-fix | 112/245 | 45.7% | 15/103 | 14.6% | 79/182 | 43.4% | 245/245 |
| AST Agent，无 fix | 77/243 | 31.7% | 42/72 | 58.3% | 17/89 | 19.1% | 243/245 |
| AST Agent，Auto-fix | 94/243 | 38.7% | 43/81 | 53.1% | 23/104 | 22.1% | 243/245 |

LambdaNet 的 `0/245` 表示当前没有可供统一复检的 TS 源码，不表示它在历史实验中没有生成
结果；它的历史有效覆盖是 213/245。

### 2.1 TypeWeaver 历史结果

历史 CSV 保留了 LambdaNet 等全部公开方法的编译结果。该表由历史 `.out/.err` 文件汇总，
不是 TypeScript 5.9.3 统一复检结果。

| 方案 | TypeCheck | 通过率 | 覆盖 |
|---|---:|---:|---:|
| TS 推断基线（tsc） | 112/241 | 46.5% | 241/245 |
| DeepTyper | 54/226 | 23.9% | 226/245 |
| LambdaNet | 24/213 | 11.3% | 213/245 |
| InCoder | 56/245 | 22.9% | 245/245 |
| SantaCoder | 77/245 | 31.4% | 245/245 |
| 纯 LLM | 52/229 | 22.7% | 229/245 |
| 旧 Pipeline | 92/222 | 41.4% | 222/245 |

LambdaNet 的 `baseline-checked` 中有 24 个 `.out` 和 189 个 `.err`，对应 `24/213`。当前
LambdaNet `baseline` 只留下错误日志，没有迁移后的 TS 根文件，因此不能用统一编译器重跑。

## 3. 去除全部编译失败样本

条件集合定义为：当前九种可统一复检的方法中至少有一种方法能够编译通过。245 个包中
保留 136 个，删除 109 个所有方法都无法通过的包。LambdaNet 因缺少 TS 源文件没有参与
该集合的筛选。

| 方案 | TypeCheck | 通过率 | Accuracy | Acc% | AnyRate | any% | 覆盖 |
|---|---:|---:|---:|---:|---:|---:|---:|
| TS 推断基线（tsc） | 108/135 | 80.0% | 36/116 | 31.0% | 61/177 | 34.5% | 135/136 |
| DeepTyper | 54/135 | 40.0% | 21/42 | 50.0% | 18/60 | 30.0% | 135/136 |
| InCoder | 55/136 | 40.4% | 12/23 | 52.2% | 7/30 | 23.3% | 136/136 |
| SantaCoder | 76/136 | 55.9% | 39/71 | 54.9% | 26/97 | 26.8% | 136/136 |
| 纯 LLM | 96/130 | 73.8% | 53/73 | 72.6% | 4/77 | 5.2% | 130/136 |
| AST 标准，无 fix | 95/136 | 69.9% | 14/89 | 15.7% | 67/156 | 42.9% | 136/136 |
| AST 标准，Auto-fix | 112/136 | 82.4% | 15/103 | 14.6% | 79/182 | 43.4% | 136/136 |
| AST Agent，无 fix | 77/135 | 57.0% | 42/72 | 58.3% | 17/89 | 19.1% | 135/136 |
| AST Agent，Auto-fix | 94/135 | 69.6% | 43/81 | 53.1% | 23/104 | 22.1% | 135/136 |

第二张表是条件分析，不能替代全量结果。因为样本集合由各方法的编译结果共同决定，
增加或删除一种方法都可能改变这 136 个包。Accuracy 和 AnyRate 没有变化，是因为被
删除的 109 个包原本就没有进入任何方法的 own-pass Accuracy 统计。

## 4. 各方法的输入差异

| 方法 | 原始输入 | 送入编译器的内容 | 是否修复 |
|---|---|---|---|
| TS 推断基线（tsc） | 原始 JS | 原始 JS，由 TypeScript 自己推断并检查类型 | 无 |
| DeepTyper | 原始 JS | DeepTyper 生成逐文件类型预测 CSV，再由 TypeWeaver 将类型织入后得到的 TS | 无 |
| LambdaNet | 原始 JS | LambdaNet 预测经 TypeWeaver 织入得到的 TS；当前只保留历史检查结果 | 无 |
| InCoder | 原始 JS | InCoder 已生成的 TS 迁移结果 | 无 |
| SantaCoder | 原始 JS | SantaCoder 已生成的 TS 迁移结果 | 无 |
| 纯 LLM | 原始 JS | `LLM-out/baseline` 中已有的纯 LLM TS 迁移结果 | 无 |
| AST 标准，无 fix | 原始 JS | 标准类型图推导结果按 TypeScript AST 位置写回后得到的 TS | 无 |
| AST 标准，Auto-fix | 标准模式生成的 TS | 根据编译诊断定位类型节点，将相关类型降级为 `any` 后的 TS | 最多 5 轮 |
| AST Agent，无 fix | 原始 JS | Agent 公平候选进入类型图，再按 TypeScript AST 位置写回后得到的 TS | 无 |
| AST Agent，Auto-fix | Agent 模式生成的 TS | 对 Agent TS 执行相同的局部类型降级 | 最多 5 轮 |

### 4.1 TS 推断基线

`tsc` 基线与其他方法的输入形式不同。它不先生成完整 TS，而是在原始 JS 上额外开启：

```text
--allowJs --checkJs
```

然后由 TypeScript 推断类型、检查 JS 并生成声明。该设置沿用 TypeWeaver 对 `tsc`
基线的定义，但它不是完整的 JS 到 TS 迁移方法，因此不能把它理解成迁移质量的理论上限。

### 4.2 TypeWeaver 公开基线

- DeepTyper 先预测类型，再通过 TypeWeaver 的统一织入器把预测结果写入 JS。
- LambdaNet 使用同类的“预测后织入”流程；当前报告只能引用历史 `.out/.err`，不能统一复检。
- InCoder 和 SantaCoder 使用各自已经生成的 TS 源码产物。
- 纯 LLM 使用已有 `LLM-out/baseline` 产物，本次评测没有重新调用模型，也没有做 Auto-fix。
- 除缺少 TS 源码的 LambdaNet 外，其他公开基线都使用当前统一编译器重新编译，不复用
  历史 CSV 中的通过状态。

### 4.3 当前 AST2Type 方法

标准模式只使用静态类型图推导，不调用 LLM。Agent 模式使用公平候选：LLM 结果进入
类型图，但候选中不加入 Ground Truth 类型。两种模式最终都通过 TypeScript AST 中的
文件位置和源码位置写回函数参数及返回类型。

Auto-fix 不修改函数调用、参数数量、模块导入或运行时代码。它解析 TypeScript 编译诊断，
定位与诊断关联的类型节点，只把能够安全定位的类型替换为 `any`，然后用同一个编译器
重新检查，最多执行 5 轮。

## 5. 编译通过率测试方法

除输入为 JS 的 `tsc` 基线以及当前无法复检的 LambdaNet 外，其余当前方法都按以下方式测试：

1. 收集一个包内全部 `.ts`、`.tsx`、`.mts` 和 `.cts` 文件；
2. 排除 `.d.ts`、`.git` 和 `node_modules`；
3. 将整个包的源文件作为同一次 `tsc` 调用的根文件；
4. 只有退出码为 0 且没有 TypeScript 诊断时，整个包才记为 PASS；
5. 任意一个文件仍有错误，整个包都记为 TYPE_ERROR；
6. 编译失败后不保留部分生成的 `.d.ts`，也不进行自动重试。

统一编译参数为：

```text
--pretty false
--esModuleInterop
--moduleResolution bundler
--module es2015
--target es6
--lib es2021,dom
--jsx preserve
--skipLibCheck
--declaration
--emitDeclarationOnly
--noEmitOnError
```

`tsc` 基线使用相同公共参数和声明生成参数，但根文件为 `.js`，并额外增加
`--allowJs --checkJs`。修正后的 `tsc=108/241` 是按该合同重新运行的结果；旧 CSV 中的
`112/241` 来自旧编译环境，不再混入当前表格。

历史 TypeWeaver 结果的生成方式是：每个方法对每个包执行一次整包 `tsc`，成功时写入
`baseline-checked/<包>.out`，失败时写入 `<包>.err`；`summarize_results.py` 再将 `.out`
记为 1、`.err` 记为 0，生成 `typecheck.<方法>.csv`。TS 推断基线检查原始 JS 并开启
`--allowJs --checkJs`，其他方法检查各自迁移后生成的 TS。历史 CSV 没有保存准确的
TypeScript 版本，因此与当前 5.9.3 统一复检分表报告。

## 6. 结果解释

| 观察 | 解释 |
|---|---|
| AST 标准 Auto-fix 的全量通过率为 45.7%，略高于 `tsc` 的 44.8% | 两者只相差 4 个通过包，基本处于同一水平 |
| AST 标准 Auto-fix 的 Accuracy 只有 14.6% | 较高通过率不能说明类型推导更准确 |
| AST 标准 Auto-fix 的 AnyRate 为 43.4% | 它通过更宽松的类型和 Auto-fix 换取了一部分编译通过率 |
| Agent 无 fix 的 Accuracy 为 58.3% | Agent 类型更准确，但生成 TS 的整体编译通过率低于标准模式 |
| 纯 LLM 的 Accuracy 最高 | 它只有 229 个全量覆盖和 130 个条件集合覆盖，需要同时报告覆盖率 |

因此，TypeCheck、Accuracy、AnyRate 和覆盖率必须一起报告，不能只根据编译通过率判断
一种类型推导方法更好。

## 7. 数据来源

- 当前 AST 四种方案：`TypeWeaver/data/Pipeline-out/top1k-typed-nodeps-es6-ast-matrix-v2/`
- 公开基线统一复检：`TypeWeaver/data/compile-comparison/top1k-typed-nodeps-es6-unified-ts59-v1/`
- 当前比较结果：`TypeWeaver/data/compile-comparison/top1k-typed-nodeps-es6-final-ts59-v1/comparison.json`
- 当前统一入口：`ast2type/src/cli.ts`
- 统一编译器：`ast2type/src/migration/compiler.ts`
- AST TS 生成：`ast2type/src/migration/js.ts`
- Auto-fix：`ast2type/src/migration/repair.ts`
- 当前批量实验：`TypeWeaver/experiments/ast2type/run.py`
- TypeWeaver 公开基线织入：`TypeWeaver/src/migrate_dataset/type_weaving.py`
- TypeWeaver 历史编译结果：`TypeWeaver/data/notes/csv/typecheck.*.csv`
- LambdaNet 历史检查产物：`TypeWeaver/data/LambdaNet-out/top1k-typed-nodeps-es6/baseline-checked/`

`tsc` 基线于 2026-07-29 使用相同 TypeScript 5.9.3 公共编译参数进行了干净复检。

## 8. TS 项目级补充实验

为了排除统一编译参数和缺失依赖的影响，另外对 TS 数据集进行了项目级测试。每个项目
使用自己的依赖、`tsconfig` 和 TypeScript 版本，Auto-fix 和最终评测共享同一编译环境。
`personal` 缺少私有依赖和上层仓库文件，因此不纳入统计。

| 项目 | Ground Truth | Raw 错误 | 项目级 Auto-fix | 错误下降 |
|---|---:|---:|---:|---:|
| mapcn | 通过 | 134 | 38 | 71.6% |
| vue | 通过 | 667 | 401 | 39.9% |
| turbolinks | 通过 | 384 | 131 | 65.9% |
| skills | 3 | 966 | 323 | 66.6% |
| **合计** | **3/4 通过** | **2151** | **893** | **58.5%** |

Raw 的主要问题是类型擦除后部分参数没有恢复标注，以及少数位置被恢复成过粗的
`object` 类型。这两类错误约占 Raw 错误的一半，Auto-fix 可以根据诊断定位参数或已有
类型标注，并将其降级为 `any`，因此参数隐式 `any` 和属性不存在错误基本被消除。

Fix 后的错误结构已经改变，主要包括：

- 原类型标注被擦除后产生的未使用 import 和失效 `@ts-expect-error`；
- 变量、类成员和函数返回值的隐式 `any`，当前定位器尚未覆盖这些声明位置；
- 推导结果生成了 `array`、`function` 等无效 TypeScript 类型名；
- 索引访问、`unknown` 和空值检查错误，这些通常需要跨位置分析，不能只修改当前标注。

因此，项目级 Auto-fix 显著减少了错误数量，但四个迁移结果仍没有整项目通过。剩余错误
中有一部分可以继续通过扩展类型位置定位来处理，例如变量、成员、返回类型以及无效类型名；
未使用代码和失效编译指令则不属于“只将报错类型位置改成 `any`”的处理范围。

本实验结果保存在：

- `TypeWeaver/data/TS-Pipeline-out/custom-ts-projects-v6/compile-results-project-autofix.json`
- `TypeWeaver/data/TS-Pipeline-out/custom-ts-projects-v6/fixed-project/auto-fix-results.json`
