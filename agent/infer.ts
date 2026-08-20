/**
 * Agent 推理引擎
 *
 * 输入: 带 value/return 槽位的候选节点
 * 输出: {id, slot, type} 数组，供 solver 回填
 */
import * as fs from "fs";
import * as path from "path";
import type { AgentFeedbackEntry, UnkSpot } from "../ast2type/solver";
import { setupProxy, chat, supportsOpenAIStructuredOutput } from "./net";
import type { AgentConfig } from "./net";

function packageContext(file: string): string {
  let current = path.dirname(file);
  for (;;) {
    try {
      const packageJson = JSON.parse(fs.readFileSync(path.join(current, "package.json"), "utf8"));
      const fields = ["name", "version", "description", "main", "module", "types", "keywords"];
      const selected = Object.fromEntries(
        fields.filter(field => packageJson[field] !== undefined)
          .map(field => [field, packageJson[field]]),
      );
      for (const readme of ["README.md", "readme.md", "README"]) {
        try {
          selected.readme = fs.readFileSync(path.join(current, readme), "utf8").slice(0, 6000);
          break;
        } catch {
          // Try the next conventional README name.
        }
      }
      return JSON.stringify(selected);
    } catch {
      const parent = path.dirname(current);
      if (parent === current) return "{}";
      current = parent;
    }
  }
}

/**
 * OpenAI Structured Outputs 要求根节点是 object，不能直接以数组作为根节点。
 * Schema 保持跨批次完全一致，便于服务端复用 schema 与 prompt 缓存。
 */
const OPENAI_FEEDBACK_SCHEMA: Record<string, unknown> = {
  type: "object",
  properties: {
    entries: {
      type: "array",
      items: {
        type: "object",
        properties: {
          id: { type: "integer" },
          slot: { type: "string", enum: ["value", "return"] },
          type: { type: "string" },
        },
        required: ["id", "slot", "type"],
        additionalProperties: false,
      },
    },
  },
  required: ["entries"],
  additionalProperties: false,
};

function buildPrompt(
  spots: UnkSpot[],
  sourceCode: string,
  structuredOutput: boolean,
  projectContext: string,
): string {
  const list = spots
    .sort((a, b) => (a.pos?.line ?? 0) - (b.pos?.line ?? 0))
    .map(
      (s) => {
        const loc = s.pos ? `line ${s.pos.line}, col ${s.pos.column}` : `offset ${s.location}`;
        return `- id=${s.id}, slot=${s.slot}, currentType=${s.type}, refinable=${Boolean(s.refinable)}, ${loc}, context="${s.context}", expr="${s.exprText}", exprKind="${s.exprKind}", morphKind="${s.morphKind}"`;
      }
    )
    .join("\n");

  const outputExample = structuredOutput
    ? '{"entries":[{"id": <编号>, "slot": "<value或return>", "type": "<类型>"}]}'
    : '[{"id": <编号>, "slot": "<value或return>", "type": "<类型>"}]';
  const outputShape = structuredOutput
    ? "只输出符合指定 Schema 的 JSON 对象，不要其他内容"
    : "只输出 JSON 数组，不要其他内容";

  return `你是 TypeScript 类型推断专家。以下是擦除类型标注后的源码，以及节点列表。

## 源码
\`\`\`typescript
${sourceCode}
\`\`\`

## 项目上下文
这是源文件所属 npm 包的 package.json 摘要，可用于判断公开 API 的惯用类型名称：
\`\`\`json
${projectContext}
\`\`\`

## 节点（需要推断类型）
${list}

## 任务
分析每个节点的类型。${outputShape}：

\`\`\`json
${outputExample}
\`\`\`

你可以使用 TypeScript 完整类型系统，包括但不限于：基础类型、数组、元组、联合/交叉类型、函数签名、泛型、字面量类型、条件类型、映射类型等。

规则：
- currentType=any 表示基础求解器的保守结果；只有有充分证据时才将它改成具体类型，不能原样返回 any
- refinable=true 且 slot=return 时，当前 boolean 可能是被擦除的类型谓词；如果源码是类型守卫，返回如 "value is Stream"，否则返回 boolean
- 类型谓词的目标类型只写在 slot=return；如果源码没有声明或 import 该目标类型，不要把同名目标类型臆造到参数上，参数保留当前 unknown 或使用源码证据支持的类型
- 尽可能精确推断，避免使用 any/object/unknown 除非确实无法推断
- slot=value 时输出该声明本身的类型；slot=return 时只输出函数返回类型，不要输出完整函数签名
- 必须原样返回每个节点的 id 和 slot
- 参数类型：看调用处传入的实参类型、参数名语义、默认值、使用方式（如 .map/.filter 中的回调参数类型与数组元素类型一致）
- 变量类型：看初始化表达式、后续赋值、属性访问模式
- 函数返回类型：综合所有 return 语句的返回值类型
- 如果所有 return 都是固定字符串/数字字面量，返回字面量联合类型；不要把可观察的返回字面量改成宽泛的 string/number
- 参数带有默认字符串/数字值时，通常返回 string/number 参数类型，不要把默认值本身当作参数类型字面量
- 回调参数：看被调方法的类型签名（如 Array#map 的回调参数类型由数组元素类型决定）
- 对象字面量：写出完整属性类型结构
- 利用 TypeScript 高级特性（泛型约束、条件类型等）来表达更精确的类型`;
}

interface BatchFailure {
  file: string;
  batch: number;
  totalBatches: number;
  error: string;
}

interface BatchJob {
  file: string;
  source: string;
  spots: UnkSpot[];
  batchNumber: number;
  totalBatches: number;
  fileTotal: number;
}

/** 原子替换 checkpoint，避免长任务中断后只留下空文件或半截 JSON。 */
function writeInferenceCheckpoint(
  file: string,
  results: AgentFeedbackEntry[],
): void {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  const temporary = `${file}.${process.pid}.tmp`;
  fs.writeFileSync(temporary, `${JSON.stringify(results, null, 2)}\n`, "utf8");
  fs.renameSync(temporary, file);
}

async function processBatch(
  job: BatchJob,
  config: AgentConfig,
  onBatchResults: (entries: AgentFeedbackEntry[]) => void,
  onBatchFailure: (failure: BatchFailure) => void,
): Promise<void> {
  const { file, source, spots, batchNumber, totalBatches } = job;
  const structuredOutput = config.provider === "openai" &&
    supportsOpenAIStructuredOutput(config.model);

  try {
    const msg = await chat(config, {
      messages: [{
        role: "user",
        content: buildPrompt(spots, source, structuredOutput, packageContext(file)),
      }],
      structuredOutput: structuredOutput
        ? { name: "type_feedback", schema: OPENAI_FEEDBACK_SCHEMA }
        : undefined,
    });

    const text = msg.content.trim();
    const m = text.match(/```(?:json)?\s*([\s\S]*?)\s*```/) || [null, text];
    const parsed = JSON.parse(m[1] || text);
    // OpenAI 严格 Schema 使用 {entries:[...]}；数组兼容 DeepSeek 和旧响应。
    const entries = Array.isArray(parsed) ? parsed : parsed?.entries;
    if (!Array.isArray(entries)) {
      throw new Error("LLM 返回不包含 feedback 数组");
    }

    // 仅在整个响应验证完成后提交，失败批次不会污染 checkpoint。
    const batchResults: AgentFeedbackEntry[] = [];
    const requested = new Map(spots.map(spot => [spot.id, spot]));
    for (const entry of entries) {
      const spot = requested.get(entry.id);
      if (!spot) {
        console.warn(`[agent] 跳过未请求的 id=${entry.id}`);
        continue;
      }
      if (entry.type && typeof entry.type === "string" && entry.type.trim()) {
        // slot 取自候选快照，不依赖模型是否正确回显。
        batchResults.push({
          id: spot.id,
          slot: spot.slot,
          type: entry.type.trim(),
          ...(spot.refinable || spot.type === "any" || spot.type === "unknown" ? { refine: true } : {}),
        });
      } else {
        console.warn(`[agent] 跳过非法类型 "${entry.type}" for id=${entry.id}`);
      }
    }

    onBatchResults(batchResults);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    // 保持旧版简洁日志格式；失败只记录一次，不再自动重试。
    console.error(`[agent] ${file} 批失败:`, message);
    onBatchFailure({
      file,
      batch: batchNumber,
      totalBatches,
      error: message,
    });
  }
}

export async function inferTypes(
  unkSpots: UnkSpot[],
  config: AgentConfig,
  batchSize = 30,
  onProgress?: (file: string, done: number, total: number) => void,
  concurrency = 20,
  inferOutputPath?: string,
): Promise<AgentFeedbackEntry[]> {
  if (!Number.isInteger(batchSize) || batchSize <= 0) {
    throw new Error(`Invalid Agent batch size ${batchSize}; expected a positive integer`);
  }
  if (!Number.isInteger(concurrency) || concurrency <= 0) {
    throw new Error(`Invalid Agent concurrency ${concurrency}; expected a positive integer`);
  }

  await setupProxy();
  console.log(`[agent] provider=${config.provider}, model=${config.model}`);

  // 按文件分组
  const byFile = new Map<string, UnkSpot[]>();
  for (const s of unkSpots) {
    const list = byFile.get(s.file) || [];
    list.push(s);
    byFile.set(s.file, list);
  }

  const files = Array.from(byFile.entries());
  const results: AgentFeedbackEntry[] = [];
  const failures: BatchFailure[] = [];

  // 将文件预先展开为全局批次队列。同一文件的批次彼此独立，不需要串行等待；
  // source 字符串只读取一次并由各 job 共享，避免额外的本地 I/O 和内存复制。
  const jobs: BatchJob[] = [];
  for (const [file, spots] of files) {
    const totalBatches = Math.ceil(spots.length / batchSize);
    if (!fs.existsSync(file)) {
      console.error(`[agent] 源码不存在: ${file}，跳过 ${spots.length} 个节点`);
      failures.push({
        file,
        batch: 1,
        totalBatches,
        error: "source file does not exist",
      });
      onProgress?.(file, spots.length, spots.length);
      continue;
    }

    const source = fs.readFileSync(file, "utf-8");
    for (let i = 0; i < spots.length; i += batchSize) {
      jobs.push({
        file,
        source,
        spots: spots.slice(i, i + batchSize),
        batchNumber: Math.floor(i / batchSize) + 1,
        totalBatches,
        fileTotal: spots.length,
      });
    }
  }

  const c = Math.min(concurrency, jobs.length);
  console.log(`[agent] 共 ${unkSpots.length} 个节点，分 ${files.length} 个文件处理（并发 ${c}）`);

  if (inferOutputPath) {
    writeInferenceCheckpoint(inferOutputPath, results);
  }

  // 信号量并发：worker 一空闲立即取下一个批次，不让大文件形成串行长尾。
  let idx = 0;
  const completedByFile = new Map<string, number>();
  async function worker(): Promise<void> {
    while (idx < jobs.length) {
      const i = idx++;
      const job = jobs[i];
      await processBatch(
        job,
        config,
        batchResults => {
          const previousLength = results.length;
          results.push(...batchResults);
          try {
            if (inferOutputPath) {
              writeInferenceCheckpoint(inferOutputPath, results);
            }
          } catch (error) {
            // 保持内存结果与最后一个完整 checkpoint 一致。
            results.length = previousLength;
            throw error;
          }
        },
        failure => failures.push(failure),
      );

      const done = Math.min(
        (completedByFile.get(job.file) || 0) + job.spots.length,
        job.fileTotal,
      );
      completedByFile.set(job.file, done);
      onProgress?.(job.file, done, job.fileTotal);
    }
  }

  await Promise.all(Array.from({ length: c }, () => worker()));

  if (inferOutputPath) {
    writeInferenceCheckpoint(inferOutputPath, results);
  }

  if (failures.length > 0) {
    const examples = failures
      .slice(0, 3)
      .map(failure => `${failure.file} ${failure.batch}/${failure.totalBatches}: ${failure.error}`)
      .join("; ");
    throw new Error(
      `${failures.length} Agent batches failed; ` +
      `${results.length} partial feedback entries were checkpointed` +
      (examples ? `; ${examples}` : ""),
    );
  }

  return results;
}
