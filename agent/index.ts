/**
 * ast2type Agent - LLM 辅助类型推断
 *
 * 读取 solver 产出的 blindspots.json，结合 erased 源码，调用 LLM 推断声明类型，
 * 输出 feedback.json 供 solver 回填使用。
 *
 * 用法:
 *   npx tsx agent/index.ts \
 *     --blindspots output/round1/blindspots.json \
 *     --sourcedir /path/to/erased_sources \
 *     --output output/feedback.json
 */

import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";
import { setupProxy, chat } from "./net";

// ========== 类型定义 ==========

interface Blindspot {
  id: number;
  identifier: string;
  kind: string;
  offset: number;
  pos: { start: { line: number; character: number } } | null;
  file: string;
  context: string;
  function?: string;
}

interface FeedbackEntry {
  id: number;
  type: string;
}

const VALID_TYPES = ["number", "string", "boolean", "void", "any", "undefined"];

// ========== LLM prompt ==========

function buildPrompt(blindspots: Blindspot[], sourceCode: string): string {
  const list = blindspots
    .sort((a, b) => (a.pos?.start.line ?? 0) - (b.pos?.start.line ?? 0))
    .map(
      (b) =>
        `  - id=${b.id} | ${b.kind} "${b.identifier}"${
          b.function ? ` (函数: ${b.function})` : ""
        } | 第${b.pos?.start.line ?? "?"}行${b.pos?.start.character ?? "?"}列`
    )
    .join("\n");

  return `你是 TypeScript 类型推断专家。以下是擦除类型标注后的源码，以及所有声明节点的位置。

## 源码
\`\`\`typescript
${sourceCode}
\`\`\`

## 声明节点（需要推断类型）
${list}

## 任务
分析每个声明节点在源码中的用法（参数使用方式、返回值、赋值等），推断其 TypeScript 类型。
只输出 JSON 数组，不要其他内容：

\`\`\`json
[
  {"id": <编号>, "type": "<number|string|boolean|void|any|undefined>"},
  ...
]
\`\`\`

规则：
- 参数类型看调用处的实参类型
- 变量类型看初始化表达式
- 函数返回类型看 return 语句
- 无法确定的用 any`;
}

// ========== 主流程 ==========

async function main() {
  const program = new Command();
  program
    .requiredOption("--blindspots <path>", "blindspots.json 路径")
    .requiredOption("--sourcedir <dir>", "erased 源码目录")
    .option("--output <path>", "feedback.json 输出路径", "output/feedback.json")
    .option("--batch-size <n>", "每批最大盲点数量", "30")
    .option("--api-key <key>", "API Key (或设环境变量 DEEPSEEK_API_KEY)");
  program.parse(process.argv);

  const opts = program.opts();
  const apiKey =
    opts.apiKey || process.env.DEEPSEEK_API_KEY;
  if (!apiKey) {
    console.error("请设置 DEEPSEEK_API_KEY 或通过 --api-key 传入");
    process.exit(1);
  }

  setupProxy();

  // 1. 读盲点
  const blindspots: Blindspot[] = JSON.parse(
    fs.readFileSync(opts.blindspots, "utf8")
  );
  console.log(`读取 ${blindspots.length} 个盲点`);

  // 2. 按文件分组
  const byFile = new Map<string, Blindspot[]>();
  for (const b of blindspots) {
    const list = byFile.get(b.file) || [];
    list.push(b);
    byFile.set(b.file, list);
  }
  console.log(`分布在 ${byFile.size} 个文件中`);

  // 3. 逐个文件推断
  const allFeedback: FeedbackEntry[] = [];
  const batchSize = parseInt(opts.batchSize, 10);

  // 路径解析：blindspots 中的 file 可能含 _output 目录后缀，需要映射回 erased 源码目录
  function resolveSrc(blindspotFile: string): string | null {
    // 尝试 1: 直接拼接
    const direct = path.join(opts.sourcedir, blindspotFile);
    if (fs.existsSync(direct)) return direct;

    // 尝试 2: 移除 _output 后缀（如 erase_output → erase）
    const stripped = blindspotFile.replace(/(_erase)_output\b/, "$1");
    const strippedPath = path.join(opts.sourcedir, stripped);
    if (fs.existsSync(strippedPath)) return strippedPath;

    // 尝试 3: 仅用 basename 在 sourcedir 下递归查找
    const basename = path.basename(blindspotFile);
    function find(dir: string): string | null {
      if (!fs.existsSync(dir)) return null;
      for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
        const fp = path.join(dir, entry.name);
        if (entry.isFile() && entry.name === basename) return fp;
        if (entry.isDirectory()) {
          const r = find(fp);
          if (r) return r;
        }
      }
      return null;
    }
    return find(opts.sourcedir);
  }

  for (const [file, spots] of byFile) {
    const srcPath = resolveSrc(file);
    if (!srcPath) {
      console.warn(`源码不存在: ${file}，跳过 ${spots.length} 个盲点`);
      continue;
    }
    const sourceCode = fs.readFileSync(srcPath, "utf8");
    console.log(`  ${path.relative(opts.sourcedir, srcPath)}: ${spots.length} 个盲点`);

    // 分批处理（一个文件可能有很多盲点）
    for (let i = 0; i < spots.length; i += batchSize) {
      const batch = spots.slice(i, i + batchSize);
      const prompt = buildPrompt(batch, sourceCode);

      try {
        const msg = await chat(apiKey, {
          messages: [{ role: "user", content: prompt }],
        });

        const text = msg.content.trim();
        // 提取 JSON（LLM 可能包在 ```json 中）
        const jsonMatch = text.match(/```(?:json)?\s*([\s\S]*?)\s*```/) || [null, text];
        const entries: FeedbackEntry[] = JSON.parse(jsonMatch[1] || text);

        if (!Array.isArray(entries)) throw new Error("返回不是数组");

        for (const e of entries) {
          if (VALID_TYPES.includes(e.type)) {
            allFeedback.push(e);
          } else {
            console.warn(`非法类型 "${e.type}" for id=${e.id}，已跳过`);
          }
        }
        console.log(`  ${file}: 批 ${Math.floor(i / batchSize) + 1} → ${entries.length} 条`);
      } catch (err: any) {
        console.error(`  ${file} 批失败:`, err.message);
      }
    }
  }

  // 4. 写 feedback.json
  const outDir = path.dirname(opts.output);
  fs.mkdirSync(outDir, { recursive: true });
  fs.writeFileSync(opts.output, JSON.stringify(allFeedback, null, 2));
  console.log(
    `\n完成: ${allFeedback.length}/${blindspots.length} 条推断 → ${opts.output}`
  );
}

main().catch((e) => {
  console.error("Agent 错误:", e.message);
  process.exit(1);
});
