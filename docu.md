# ast2type 设计架构

## 项目目标

从**无类型标注**的 JS/TS 源码推导类型。核心做法：将程序语义编码为类型约束图，通过约束传播推断每个表达式的类型。

## 整体流水线

```
原始 TS 源码
  │
  ├── eraseAnnotation.ts    擦除类型标注 → erased 源码
  └── _groundtruth.json     原始标注（用于评估）
        │
        ▼
      code2ast.ts           生成 AST JSON (.ast.json)
        │
        ▼
      ast2type.ts           类型推导引擎
        │
        ├── typeinfo.json    已推导类型
        ├── unkinfo.json     未推导表达式
        ├── typegraph.json   完整类型图
        └── evaluation.json  评估报告
```

## 引擎内部架构

```
                     ast2type/
                     ├── meta.ts       节点元数据
AST ─→ firstPass ─→  ├── fact.ts       语义事实发射
      secondPass ─→   ├── rule.ts       事实→图效应
                      ├── graph.ts      类型图
                      ├── strategy.ts   传播策略
                      ├── nType.ts      类型节点
                      └── solver.ts     协调求解
```

### 推导流程

1. **firstPass**：为所有 AST 节点分配 varId，收集导出映射
2. **secondPass**：递归遍历 AST，通过 `Emitter` 发射 22 种语义事实（Facts）
3. **Rule**：25 条规则将 Fact 转为 `GraphEffect`（genType / addEdge / mergeNode 等）
4. **Solver**：工作列表循环 — 沿 sameType 边传播类型，沿结构边（属性/数组/参数/返回）扩展类型，迭代至不动点
5. **Output**：序列化类型图、已知/未知注解、评估报告

---

## Agent 辅助推导：盲找 + 回填

### 问题

solver 的传播能力取决于**入口**有类型信息。但 secondPass 只对含有 `v8Kind` 的表达式节点（字面量、二元运算、属性访问等）产生 Fact，**声明类节点**（Parameter、VariableDeclaration、函数声明）不会产生类型约束。擦除标注后，这些声明节点完全没有类型信息，导致传播链从源头断裂。

典型表现：evaluation 中大量 Missing（solver 推不出类型），Coverage 仅 ~38%。

### 思路

将声明节点的类型推断外包给 LLM agent，再将结果回填到 solver：

1. **盲找**：输出所有声明节点的位置信息（blindspots.json）
2. **LLM** 读 erased 源码 + blindspots.json → 推断每个声明的类型
3. **回填**：将 LLM 结果（feedback.json）注入 solver 作为新的传播入口
4. **重推导**：solver 从回填的类型出发，传播到下游表达式
5. **迭代**：仍有 unknown 则继续盲找→LLM→回填

### 全流程图

```
erased 源码
  │
  ▼ code2ast + ast2type -o round1
  ├── round1/blindspots.json      ← [新] 声明盲点
  ├── round1/typeinfo.json        ← 已推导表达式类型
  └── round1/unkinfo.json         ← 未推导表达式
        │
        ▼ LLM agent 读取 erased 源码 + blindspots.json
        ▼ 产出 feedback.json  [{id, type}, ...]
        │
  ▼ ast2type -i same_ast -o round2 -f feedback.json
  ├── round2/typeinfo.json        ← 更多类型（含传播结果）
  └── round2/unkinfo.json         ← 仍未知的节点
        │
        ▼ ... 可继续迭代
```

### blindspots.json

遍历 `meta.declKind`，收集所有声明类标识符。输出格式（与 ground truth JSON 同构便于 LLM 消费）：

```json
[
  {
    "id": 108,
    "identifier": "a",
    "kind": "Parameter",
    "offset": 13,
    "pos": { "start": { "line": 1, "character": 14 } },
    "file": "/path/to/src/",
    "function": "add",
    "context": "a"
  }
]
```

覆盖 7 种声明：

| kind | 含义 | id 来源 |
|------|------|---------|
| `Parameter` | 函数参数 | Identifier 子节点 varId |
| `VariableDeclaration` | 变量声明 | Identifier 子节点 varId |
| `FunctionDeclaration` | 命名函数 | 函数名 Identifier varId |
| `MethodDeclaration` | 类方法 | 方法名 Identifier varId |
| `MethodSignature` | 接口方法 | 方法名 Identifier varId |
| `ArrowFunction` | 箭头函数 | 函数体节点 varId |
| `FunctionExpression` | 函数表达式 | 函数体节点 varId |

### 跟踪机制 (meta.declKind)

secondPass 中每个声明 handler 额外在 `meta.declKind` 上记录标识符 varId → 声明种类：

```
Parameter handler         →  meta.declKind.set(paramIdNode.varId, "Parameter")
VariableDeclaration       →  meta.declKind.set(left.varId, "VariableDeclaration")
FunctionDeclaration       →  meta.declKind.set(idNode.varId, "FunctionDeclaration")
MethodDeclaration         →  meta.declKind.set(propIdNode.varId, "MethodDeclaration")
MethodSignature           →  meta.declKind.set(methodIdNode.varId, "MethodSignature")
ArrowFunction             →  meta.declKind.set(node.varId, "ArrowFunction")
FunctionExpression        →  meta.declKind.set(node.varId, "FunctionExpression")
```

### feedback.json

与 `inferinfo.json` 同构：

```json
[
  { "id": 108, "type": "number" },
  { "id": 129, "type": "string" }
]
```

其中 `id` 对应 `blindspots.json` 中的 `id`。当前支持的类型值：`number`、`string`、`boolean`、`void`、`any`、`undefined`。

### injectFeedback() 内部机制

```typescript
injectFeedback(feedbackPath):
  for each {id, type}:
    syntheticVarId = typeVarCounter++        // 创建合成节点
    emit.allocPrimitive(syntheticVarId, typeId)   // 分配 basic type
    emit.flow(syntheticVarId, targetVarId)         // 绑定到目标标识符
```

为什么用 `Flow` 边而非 `Annot` 边：
- `Flow` → Rule 产生 `sameType` 边 → solver 沿 sameType 传播类型
- 如果目标 varId 已被其他变量 bind（如 `const x = 42`），sameType 边会将反馈类型与已有类型 merge
- `Annot` 边不会参与传播，类型被"钉死"在标注节点上，下游不可达

### CLI 选项

```
-i, --input <dir>         AST JSON 目录（必需）
-o, --output <dir>        输出目录（默认 ./output）
-g, --groundtruth <path>  ground truth JSON（评估用）
-f, --feedback <path>     LLM 反馈 JSON（回填用，新）
```

main() 执行顺序：

```
firstPass → secondPass → injectGroundTruth (-g) → injectFeedback (-f) → solve → output
```

### 与 ground truth 的协作

- `-g groundtruth` 注入原始标注作为 `Annot` 边 → solver 用它们做评估
- `-f feedback` 注入 LLM 推断作为 `Flow` 边 → solver 用它们做传播
- **两者独立运行**，互不干扰。feedback 的回填类型可以和 ground truth 的标注比较（evaluation 自动计算）

### 实现涉及的文件

| 文件 | 改动 |
|------|------|
| `ast2type/meta.ts` | +`declKind` 字段 |
| `ast2type/ast2type.ts` | +`-f` CLI / +`injectFeedback()` / +7 处 `meta.declKind.set()` |
| `ast2type/solver.ts` | +`blindspots.json` 输出逻辑 |

## 附录：引擎各模块要点

### meta.ts — 元数据
每个 varId 存储：`file`, `pos`, `offset`, `kind`, `text`, `context`, `v8Kind`, `funcName`, `paramName`, `propName`, `funcParamMap`, `funcBindMap`, `declKind`

### fact.ts — 事实系统
22 种事实（AllocPrimitive, AllocLiteral, Flow, SameID, Annot, Call, Param, Arg, Prop, ...），`Emitter` 提供类型安全的发射方法。

### rule.ts — 规则引擎
25 条规则将 Fact → `GraphEffect`（genType, addEdge, delayEdge, mergeNode, setVoid）。

### graph.ts — 类型图
`TypeGraph`：`nodes` (VarId→NodeState) + `toEdges`/`fromEdges` + `delayEdges`。核心方法 `extend()` 沿结构边（property, ArrayElement, param, return）传播类型。`evaluate()` 比较 annotation 边与 ground truth，输出准确率/覆盖率。

### nType.ts — 类型系统
`tNodeStore` 统一管理 7 种类型：primitive, literal, array, function, union, object, enum。通过规范序列化确保唯一性，支持循环引用。

### strategy.ts — 传播策略
`DeterminantStrategy`：`propagate()` 沿 sameType/ArgToParam 边推送类型，`merge()` 将多候选合并为联合类型。

### solver.ts — 求解器
工作列表循环（最大 10^6 迭代）：
```
worklist.pop → strategy.propagate(node) → graph.extend(node)
```
最后 `output()` 序列化所有产物。
