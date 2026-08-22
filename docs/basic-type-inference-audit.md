# 基础类型推断审计

## 评测口径

本文使用 TypeWeaver 的官方函数签名比较器。它按 `函数名 + 参数个数` 匹配声明，逐项做
类型字符串精确比较，跳过 ground truth 为 `any` 的位置。全量数据包含 245 个包；即使包
编译失败，也使用 `noEmitOnError=false` 生成声明后统计 Accuracy，避免只看通过包造成筛选偏差。

## 发现的问题

v5 Agent 全量输出包含 212 个可检查类型，其中 114 个正确、98 个错误。宽松筛选后有 46
个错误的 ground truth 属于基础类型、函数或数组，但这些错误不能全部归因于求解器：

| 类别 | 示例 | 结论 |
|---|---|---|
| 内建调用语义缺失 | `RegExp.test(...)` 的返回值为 `unknown` | 真实推断缺口 |
| 字符串调用链中断 | `String(x).replace(...)` 的返回值为 `unknown` | 真实推断缺口 |
| 可变赋值未加宽 | `flag = true` 被保留成字面量 `true` | 真实推断缺口 |
| 字符串值包含源码引号 | `'@'` 被存成值 `"'@'"` | 字面量解析错误 |
| 可选参数表示不同 | 推断为 `string | undefined`，比较器把 `x?: string` 读成 `string` | 评测表示差异 |
| 自定义名称不同 | `Change[]` 与 `IDiffResult[]` | 不是基础类型错误 |
| ground truth 比运行时更窄 | `String(url)` 实际接受任意值，但答案要求 `url: string` | API 契约无法只靠运行时操作确定 |

## 本轮修复

1. 调用事实现在记录未被遮蔽的全局函数名，以及属性调用的接收者和方法名。
2. 基础规则直接识别 `String`、`Number`、`Boolean` 的返回类型。
3. 对高置信度字符串方法补充接收者和返回类型；数组与字符串共有的方法不反推接收者类型。
4. 接收者已经确定为正则表达式时，`.test()` 返回 `boolean`。
5. 普通可变赋值把字符串、数字和布尔字面量加宽为对应基础类型。
6. 使用 TypeScript scanner 读取字符串 token 的真实值，不再把源代码引号存入类型值。
7. 仅对“`typeof` 类型不符后立即抛错”的前置条件回填基础参数类型；普通分支不做全局收窄。
8. 对象字面量的花括号不再被误当成词法作用域，带对象默认参数的函数不会提前丢失参数绑定。

这些规则进入基础 typegraph 求解，而不是只在最终迁移文本中替换类型。

## 结果

四个定向包用于验证本轮规则，比较项数量前后均为 16：

| 标准模式 | Correct / Checked | Accuracy | AnyRate |
|---|---:|---:|---:|
| 修改前 | 2 / 16 | 12.5% | 0.0% |
| 修改后 | 7 / 16 | 43.8% | 0.0% |

稳定增加的 5 项分别来自 `encodeurl` 1 项、`media-typer` 3 项和
`merge-descriptors` 1 项。`cjs-module-lexer` 的错误字符串值也已修正，但标准模式在该包的
正确项总数没有变化。

随后用 8 个包含 `typeof` 前置条件的包验证守卫和作用域规则。在 31 个固定比较项上，
正确项从 v6 的 11 个增加到 16 个；新增项分别来自 `cookie`、`detect-newline`、
`is-absolute-url`、`prepend-http` 和 `require-from-string`，没有包出现正确项下降。

245 包标准模式全量结果如下。该表是当前工作树相对历史 std-v7 的累计变化，还包含此前
已经存在于工作树中的谓词和迁移规则，不能把全部增量归因于本轮基础规则。

| 标准模式 | TypeCheck | Accuracy | AnyRate | 可比较项 |
|---|---:|---:|---:|---:|
| 历史 std-v7 | 33 / 245 | 44 / 237（18.6%） | 8 / 245（3.3%） | 237 |
| 当前工作树 v8 | 37 / 245 | 75 / 237（31.6%） | 8 / 245（3.3%） | 237 |

在同一当前工作树内，加入 `typeof` 前置条件和作用域修复前的 v6 为 `70/237`；因此这两项
规则的全量净增益是 5 个正确类型，比较分母和 Any 数量均未变化。

结果文件：

- 历史标准模式：`/tmp/std-v7-all/std-raw/accuracy.json`
- 内建调用和赋值规则全量评测（v6）：`/tmp/basic-inference-v6-full-std-all/std-raw/accuracy.json`
- 当前全量生成（v8）：`/tmp/basic-inference-v8-full-std`
- 当前全量声明评测（v8）：`/tmp/basic-inference-v8-full-std-all/std-raw/accuracy.json`
- 当前四包定向评测：`/tmp/basic-inference-v6-targeted-all`
- `typeof` 与作用域定向评测：`/tmp/basic-inference-v8-scope-targeted-all`

## 尚未解决

- 普通 `typeof x === "string"` 分支目前不会构造完整控制流联合类型；只支持抛错式前置条件。
- 构造器实例、自定义接口名和第三方库类型仍需要跨文件符号信息或 Agent。
- 官方比较器不能区分同名同参数个数的重载，并且对多行声明、可选参数的处理较粗糙。
- Agent 偶尔返回未声明泛型（例如 `T`）；这属于 Agent 反馈校验问题，不应由基础规则猜测修复。
