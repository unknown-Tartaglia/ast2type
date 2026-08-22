# JavaScript 类型推导工具测试报告

## 1. 报告范围

本报告对应提交 `b083197`，包含：

1. 工具可运行性和回归测试；
2. TypeWeaver `top1k-typed-nodeps-es6` 全量 245 包测试；
3. 与 DeepTyper、LambdaNet、InCoder、SantaCoder 的共同包比较；
4. 华为二阶段验收包中 JetStream2/WSL 和 personal workload 的已有统计复核。

报告区分“当前版本新测结果”和“验收包历史结果”，不混用两个版本的数字。

## 2. 测试环境

| 项目 | 环境 |
|---|---|
| Node.js | v22.23.1 |
| npm | 10.9.8 |
| TypeScript | 5.9.3 |
| ast2type | commit `b083197` |
| TypeWeaver 数据集 | `top1k-typed-nodeps-es6`，245 个包 |
| Agent | OpenAI `gpt-5.6-sol`，fair 候选 |
| Agent 选项 | `signature-only`、`refine-any`、共识 2 轮 |
| 编译环境 | TypeWeaver dependency-eval 环境；统一 TypeScript 编译契约 |

可复现实验命令：

```bash
cd TypeWeaver/experiments/ast2type
python3 run.py \
  --source-dir ../../data/original/top1k-typed-nodeps-es6 \
  --output-dir /tmp/typeweaver-agent-consensus2 \
  --modes agent --stages raw \
  --workers 2 --compile-workers 8 \
  --agent-provider openai \
  --agent-signature-only --agent-refine-any \
  --agent-consensus-rounds 2 --agent-concurrency 10
```

生成结果再使用统一依赖环境复核；报告中的 Accuracy 使用 TypeWeaver 官方函数签名比较器。

## 3. 工具可运行性

| 检查 | 结果 |
|---|---|
| `npm run typecheck` | 通过 |
| `npm test` | 49/49 回归测试通过 |
| 标准迁移 Demo | 可运行，输出迁移报告和 TypeScript 源码 |
| Agent provider 解析 | DeepSeek/OpenAI 配置、SSE、结构化输出回归通过 |
| 递归类型图 | 已增加环检测，避免 utility 包栈溢出 |

## 4. TypeWeaver 指标口径

```text
Accuracy = Correct / Checked
非 Any 率 = Checked / (Checked + Any)
AnyRate = Any / (Checked + Any)
调和平均 = 2 × Accuracy × 非 Any率 / (Accuracy + 非 Any率)
```

编译通过率按包统计：包内任意 TypeScript 源文件有错误，整个包记为失败。没有生成 TS 的
包不计为通过，并单独体现在生成覆盖中。

## 5. TypeWeaver 全量结果

四种历史方法的计数来自 TypeWeaver 保存的官方 CSV；当前 Agent-consensus2 是在同一数据集
上重新运行并使用统一依赖环境编译的结果。SantaCoder 的历史 CSV 汇总字段存在不一致，本文
按原始计数 `39/144` 计算 Accuracy。

| 方法 | TypeCheck | 通过率 | Accuracy | 非 Any 率 | AnyRate | 调和平均 | Accuracy 覆盖 |
|---|---:|---:|---:|---:|---:|---:|---:|
| DeepTyper | 54/245 | 22.04% | 85/209 = 40.67% | 72.32% | 27.68% | 52.06% | 54/245 |
| LambdaNet | 24/245 | 9.80% | 104/227 = 45.81% | 100.00% | 0.00% | 62.84% | 53/245 |
| InCoder | 57/245 | 23.27% | 34/105 = 32.38% | 81.40% | 18.60% | 46.33% | 38/245 |
| SantaCoder | 78/245 | 31.84% | 39/144 = 27.08% | 75.79% | 24.21% | 39.91% | 42/245 |
| 当前 Agent-consensus2 | 49/245 | 20.00% | 117/218 = **53.67%** | **95.61%** | **4.39%** | **68.75%** | 57/245 |

当前共识实验生成 TS 的包为 244/245，`lodash` 两次调用都遇到上游 API 502，因此在表中
按 missing 计入 245 包分母。统一评测实际产出声明的包为 243 个。

结论：当前方法在 Accuracy、非 Any 率和调和平均上优于四个历史方法中的对应全量计数，
但 TypeCheck 不是最高，且没有达到“Accuracy > 80%”的验收指标。

## 6. 与 LambdaNet 的共同包比较

LambdaNet 的迁移源文件没有完整保留，使用其 `baseline-typedefs` 声明产物作为“成功生成”
口径。LambdaNet 产出 210 包，当前方法产出 244 包，交集为 209 包；唯一不在交集中的包是
当前缺失的 `lodash`。

| 方法 | TypeCheck | 通过率 | Accuracy | 非 Any 率 | AnyRate | 调和平均 | Accuracy 覆盖 |
|---|---:|---:|---:|---:|---:|---:|---:|
| LambdaNet | 24/209 | 11.48% | 104/227 = 45.81% | 100.00% | 0.00% | 62.84% | 53/209 |
| 当前 Agent-consensus2 | 39/209 | **18.66%** | 114/200 = **57.00%** | 95.24% | 4.76% | **71.32%** | 53/209 |

当前方法在共同包上的调和平均比 LambdaNet 高 8.48 个百分点，相对提升约 13.5%；但
Accuracy 仍为 57.00%，没有达到 80%。

## 7. 与四种方法的共同包比较

五种方法都实际生成 TS 的交集为 196 包：

| 方法 | TypeCheck | 通过率 | Accuracy | 非 Any 率 | AnyRate | 调和平均 | Accuracy 覆盖 |
|---|---:|---:|---:|---:|---:|---:|---:|
| DeepTyper | 47/196 | 23.98% | 82/204 = 40.20% | 72.34% | 27.66% | 51.68% | 51/196 |
| LambdaNet | 24/196 | 12.24% | 102/223 = 45.74% | 100.00% | 0.00% | 62.77% | 52/196 |
| InCoder | 48/196 | 24.49% | 29/91 = 31.87% | 81.25% | 18.75% | 45.78% | 33/196 |
| SantaCoder | 67/196 | 34.18% | 67/131 = 51.15% | 74.43% | 25.57% | 60.63% | 38/196 |
| 当前 Agent-consensus2 | 39/196 | 19.90% | 112/196 = **57.14%** | **95.15%** | **4.85%** | **71.40%** | 52/196 |

## 8. 华为 workload 结果复核

验收包位置：`docs/华为二阶段验收/类型推导项目/`。其中 `tests/JetStream2` 包含 WSL、
SunSpider、Octane 等 JavaScript workload，`tests/personal` 包含 personal 项目。现有
`output/evaluation.json` 的统计如下：

| 总槽位 | Correct | Wrong | Missing | Any | Unknown |
|---:|---:|---:|---:|---:|---:|
| 615 | 54 | 0 | 144 | 384 | 33 |

按验收包原脚本的总量口径：

- 总量准确率：`54/615 = 8.78%`；
- 覆盖率：`(54 + 0 + 384)/615 = 71.22%`。

如果只看已经被识别为具体类型的槽位，识别域为 `Correct + Wrong = 54`，识别域准确率为
`54/54 = 100%`。但这个数字不代表整体推导质量，因为 144 个 Missing、384 个 Any 和
33 个 Unknown 被排除在分子之外。

为使它与 TypeWeaver 的非 Any 指标可比较，保守定义：

```text
workload 非 Any 率 = (Correct + Wrong) / (Correct + Wrong + Any)
                 = 54 / 438 = 12.33%
workload 类 F1 = 2 × 100% × 12.33% / (100% + 12.33%) = 21.95%
```

因此，已有 workload 产物可以证明“可识别小域的抽样准确率为 100%”，但不能证明整体
workload 达到 Accuracy > 80% 和 F1 达标；它的覆盖和非 Any 率仍然不足。该 `evaluation.json`
来自华为二阶段验收包的历史原型输出，尚未用提交 `b083197` 的当前 CLI 在完整 workload
上重跑，不能当作当前版本的最终验收结果。

## 9. 验收指标状态

| 指标 | 当前证据 | 状态 |
|---|---|---|
| 实现源码可正确运行 | TypeScript 检查通过，49 个回归测试通过 | 已满足 |
| TypeWeaver Accuracy > 80% | 当前全量 53.67%，共同包 57.14% | 未满足 |
| TypeWeaver F1 比学界最优高 10% | 全量 68.75%，LambdaNet 62.84%；相对提升约 9.4% | 接近但未满足 |
| Huawei workload 可运行 | 验收包已有旧原型输出 | 可复核基线，需当前版本重跑 |
| Huawei workload 可识别域 Accuracy > 80% | 历史识别域为 100%，但样本方法和覆盖不足 | 需规范抽样后确认 |
| Huawei workload F1 达标 | 历史保守 F1 21.95% | 未满足 |

## 10. 后续补测建议

1. 在 `tests/JetStream2` 和 `tests/personal` 上用当前 CLI 生成新的 `typeinfo.json`，固定
   文件清单、随机抽样种子和可识别类型判定规则；
2. 对抽样槽位同时记录 `Correct/Wrong/Missing/Any/Unknown`，避免只报告识别域准确率；
3. 优先减少 Missing 和 Any，再重新计算 workload 的非 Any 率和 F1；
4. TypeWeaver 方面增加高置信度类型规则和跨模块类型恢复，目标先把 Accuracy 提升到 80%；
5. 材料提交时把本报告、工具说明书、源代码 commit 和一个可重复运行的 demo 目录一起打包。

## 11. 证据位置

- 当前源码提交：`b083197`
- TypeWeaver 当前全量结果：`/tmp/consensus2-all/std-raw/summary.json`
- TypeWeaver 四方法历史计数：`TypeWeaver/data/notes/csv/accuracy.{dt,ln,ic,sc}.csv`
- LambdaNet 共同包结果：`/tmp/consensus2-lambda-common-all/std-raw/summary.json`
- 华为 workload 历史结果：`docs/华为二阶段验收/类型推导项目/output/evaluation.json`
- 验收包原始设计说明：`docs/华为二阶段验收/DESIGN.md`
