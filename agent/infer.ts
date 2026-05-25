/**
 * Agent 推理引擎 - 纯函数，无文件 I/O
 *
 * 输入: unkinfo（声明盲点 + 源码读取回调）
 * 输出: {id, type} 数组，供 solver 回填
 */
import * as fs from "fs";
import path from "path";
import { outputDir } from "../ast2type";
import { setupProxy, chat } from "./net";
import { writeJsonStream } from "../code2ast";

export interface UnkSpot {
  id: number;
  context: string;
  exprText: string;
  exprKind: string;
  morphKind: string;
  location: number;
  pos: { line: number; column: number } | null;
  type: "unknown";
  relapath: string;
  file: string;
}

function buildPrompt(spots: UnkSpot[], sourceCode: string): string {
  const list = spots
    .sort((a, b) => (a.pos?.line ?? 0) - (b.pos?.line ?? 0))
    .map(
      (s) => {
        const loc = s.pos ? `line ${s.pos.line}, col ${s.pos.column}` : `offset ${s.location}`;
        return `- id=${s.id}, ${loc}, context="${s.context}", expr="${s.exprText}", exprKind="${s.exprKind}", morphKind="${s.morphKind}"`;
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
[{"id": <编号>, "type": "<类型>"}]
\`\`\`

支持的类型格式：
- 基础: number, string, boolean, void, any, undefined, null
- 数组: number[], string[], (string|number)[] 等
- 联合: string | number, "a" | "b" | "c" 等
- 函数: (x: number) => string, () => void 等
- 对象: {x: number, y: string}
- 泛型: Promise<number>, Array<string> 等

规则：
- 尽可能精确，不要简单写 any 或 object
- 参数类型看调用处传入的实参类型
- 变量类型看初始化表达式
- 函数返回类型看 return 语句
- 回调参数看 .map/.filter/.forEach 等方法的数组元素类型
- 如果可以从上下文推断出更精确的类型，请使用复杂类型`;
}

async function processFile(
  file: string,
  spots: UnkSpot[],
  apiKey: string,
  batchSize: number,
  onProgress?: (file: string, done: number, total: number) => void
): Promise<Array<{ id: number; type: string }>> {
  if (!fs.existsSync(file)) {
    console.error(`[agent] 源码不存在: ${file}，跳过 ${spots.length} 个节点`);
    return [];
  }
  const source = fs.readFileSync(file, "utf-8");
  const results: Array<{ id: number; type: string }> = [];

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

      for (const e of entries) {
        if (e.type && typeof e.type === "string" && e.type.trim()) {
          results.push(e);
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
): Promise<Array<{ id: number; type: string }>> {
  await setupProxy();

  // 按文件分组
  const byFile = new Map<string, UnkSpot[]>();
  for (const s of unkSpots) {
    const list = byFile.get(s.file) || [];
    list.push(s);
    byFile.set(s.file, list);
  }

  const files = Array.from(byFile.entries());
  const results: Array<{ id: number; type: string }> = [];
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

  // 结果写到output/inferinfo.json，供 ast2type 主流程回读注入
  const inferOut = path.join(outputDir, "inferinfo.json");
  writeJsonStream(inferOut, results);

  return results;
}
