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

const VALID_TYPES = ["number", "string", "boolean", "function", "array", "object", "enum"];

/**
 * 
  id: number;
  identifier: string;
  kind: string;
  offset: number;
  pos: { start: { line: number; character: number } } | null;
  file: string;
  context: string;
  function?: string;
}
 */
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
[{"id": <编号>, "type": "<number|string|boolean|function|array|object|enum>"}]
\`\`\`

规则：
- 参数类型看调用处传入的实参类型
- 变量类型看初始化表达式
- 函数返回类型看 return 语句
- 回调参数看 .map/.filter/.forEach 等方法的数组元素类型`;
}

export async function inferTypes(
  unkSpots: UnkSpot[],
  apiKey: string,
  batchSize = 30,
  onProgress?: (file: string, done: number, total: number) => void
): Promise<Array<{ id: number; type: string }>> {
  setupProxy();

  // 按文件分组
  const byFile = new Map<string, UnkSpot[]>();
  for (const s of unkSpots) {
    const list = byFile.get(s.file) || [];
    list.push(s);
    byFile.set(s.file, list);
  }

  const results: Array<{ id: number; type: string }> = [];
  console.log(`共 ${unkSpots.length} 个节点，分 ${byFile.size} 个文件处理`);

  for (const [file, spots] of byFile) {
    if (!fs.existsSync(file)) {
      console.error(`[agent] 源码不存在: ${file}，跳过 ${spots.length} 个节点`);
      continue;
    }
    const source = fs.readFileSync(file, "utf-8");

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
          if (VALID_TYPES.includes(e.type)) {
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
  }

  // 结果写到output/feedback.json，供 ast2type 主流程回读注入
  const inferOut = path.join(outputDir, "inferinfo.json");
  writeJsonStream(inferOut, results);


  return results;
}
