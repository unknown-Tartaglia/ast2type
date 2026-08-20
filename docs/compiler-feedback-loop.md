# 编译反馈修复

编译反馈修复已合并到统一 CLI，不再维护单独的 Python loop 和 Agent 入口。

| 策略 | 行为 |
|---|---|
| `rules` | 用 AST/type checker 找到引发诊断的声明类型，并保守降级为 `any` |
| `agent` | 把可修复诊断和局部源码交给 LLM，逐条编译验证并回滚无效编辑 |
| `rules+agent` | 先执行确定性规则，再处理剩余局部错误 |

```bash
npm run migration -- repair <raw-typescript-project> \
  --out <fixed-project-copy> \
  --strategy rules+agent \
  --agent-provider deepseek \
  --rule-rounds 5 \
  --agent-rounds 2
```

修复结果直接输出 JSON，包含初始和最终诊断数、接受编辑数、每轮统计及最终诊断。
规则和 Agent 都复用 `src/migration/compiler.ts`，因此 auto-fix 与最终评测不会出现编译
判定口径漂移。

Agent 只接收能够定位到当前项目源码的局部类型错误。模块缺失、语法错误和项目外文件不会
交给模型。每条编辑必须使用唯一原文锚点，且只有总诊断减少、语法错误不增加、环境错误不
增加时才保留。
