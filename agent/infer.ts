/**
 * Agent 推理引擎
 *
 * 输入: 带 value/return 槽位的候选节点
 * 输出: {id, slot, type} 数组，供 solver 回填
 */
import * as fs from "fs";
import type { AgentFeedbackEntry, UnkSpot } from "../ast2type/solver";
import { setupProxy, chat } from "./net";
import { writeJsonStream } from "../code2ast";

function buildPrompt(spots: UnkSpot[], sourceCode: string): string {
  const list = spots
    .sort((a, b) => (a.pos?.line ?? 0) - (b.pos?.line ?? 0))
    .map(
      (s) => {
        const loc = s.pos ? `line ${s.pos.line}, col ${s.pos.column}` : `offset ${s.location}`;
        return `- id=${s.id}, slot=${s.slot}, ${loc}, context="${s.context}", expr="${s.exprText}", exprKind="${s.exprKind}", morphKind="${s.morphKind}"`;
      }
    )
    .join("\n");

  return `你是 TypeScript 类型推断专家。以下是擦除类型标注后的源码，以及节点列表。

## 源码
\`\`\`typescript
${sourceCode}
\`\`\`

## 节点（需要推断类型）
${list}

## 任务
分析每个节点的类型。只输出 JSON 数组，不要其他内容：

\`\`\`json
[{"id": <编号>, "slot": "<value或return>", "type": "<类型>"}]
\`\`\`

你可以使用 TypeScript 完整类型系统，包括但不限于：基础类型、数组、元组、联合/交叉类型、函数签名、泛型、字面量类型、条件类型、映射类型等。

规则：
- 尽可能精确推断，避免使用 any/object/unknown 除非确实无法推断
- slot=value 时输出该声明本身的类型；slot=return 时只输出函数返回类型，不要输出完整函数签名
- 必须原样返回每个节点的 id 和 slot
- 参数类型：看调用处传入的实参类型、参数名语义、默认值、使用方式（如 .map/.filter 中的回调参数类型与数组元素类型一致）
- 变量类型：看初始化表达式、后续赋值、属性访问模式
- 函数返回类型：综合所有 return 语句的返回值类型
- 回调参数：看被调方法的类型签名（如 Array#map 的回调参数类型由数组元素类型决定）
- 对象字面量：写出完整属性类型结构
- 利用 TypeScript 高级特性（泛型约束、条件类型等）来表达更精确的类型`;
}

async function processFile(
  file: string,
  spots: UnkSpot[],
  apiKey: string,
  batchSize: number,
  onProgress?: (file: string, done: number, total: number) => void
): Promise<AgentFeedbackEntry[]> {
  if (!fs.existsSync(file)) {
    console.error(`[agent] 源码不存在: ${file}，跳过 ${spots.length} 个节点`);
    return [];
  }
  const source = fs.readFileSync(file, "utf-8");
  const results: AgentFeedbackEntry[] = [];

  for (let i = 0; i < spots.length; i += batchSize) {
    const batch = spots.slice(i, i + batchSize);
    try {
      const msg = await chat(apiKey, {
        messages: [{ role: "user", content: buildPrompt(batch, source) }],
      });

      const text = msg.content.trim();
      const m = text.match(/```(?:json)?\s*([\s\S]*?)\s*```/) || [null, text];
      const entries = JSON.parse(m[1] || text);

      if (!Array.isArray(entries))
        throw new Error("LLM 返回不是数组");

      const requested = new Map(batch.map(spot => [spot.id, spot]));
      for (const e of entries) {
        const spot = requested.get(e.id);
        if (!spot) {
          console.warn(`[agent] 跳过未请求的 id=${e.id}`);
          continue;
        }
        if (e.type && typeof e.type === "string" && e.type.trim()) {
          // slot 取自候选快照，不依赖模型是否正确回显。
          results.push({ id: spot.id, slot: spot.slot, type: e.type.trim() });
        } else {
          console.warn(`[agent] 跳过非法类型 "${e.type}" for id=${e.id}`);
        }
      }
    } catch (err: any) {
      console.error(`[agent] ${file} 批失败:`, err.message);
    }
    onProgress?.(file, Math.min(i + batchSize, spots.length), spots.length);
  }

  return results;
}

export async function inferTypes(
  unkSpots: UnkSpot[],
  apiKey: string,
  batchSize = 30,
  onProgress?: (file: string, done: number, total: number) => void,
  concurrency = 20,
  inferOutputPath?: string,
): Promise<AgentFeedbackEntry[]> {
  await setupProxy();

  // 按文件分组
  const byFile = new Map<string, UnkSpot[]>();
  for (const s of unkSpots) {
    const list = byFile.get(s.file) || [];
    list.push(s);
    byFile.set(s.file, list);
  }

  const files = Array.from(byFile.entries());
  const results: AgentFeedbackEntry[] = [];
  const c = Math.min(concurrency, files.length);
  console.log(`[agent] 共 ${unkSpots.length} 个节点，分 ${files.length} 个文件处理（并发 ${c}）`);

  // 信号量并发：worker 一空闲立即取下一个文件，不等待整批完成
  let idx = 0;
  async function worker(): Promise<void> {
    while (idx < files.length) {
      const i = idx++;
      const [file, spots] = files[i];
      const r = await processFile(file, spots, apiKey, batchSize, onProgress);
      results.push(...r);
    }
  }

  await Promise.all(Array.from({ length: c }, () => worker()));

  if (inferOutputPath) {
    writeJsonStream(inferOutputPath, results);
  }

  return results;
}
