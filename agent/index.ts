/**
 * ast2type Agent CLI - LLM 辅助类型推断（独立命令行工具）
 *
 * 用法:
 *   npx tsx agent/index.ts \
 *     --unkinfo output/blindspots.json \
 *     --sourcedir /path/to/erased_sources \
 *     --output output/feedback.json
 *
 * 注：Agent 已集成到 ast2type 主流程（--agent），本 CLI 仅用于外部调试。
 */

import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";
import { inferTypes, UnkSpot } from "./infer";

async function main() {
  const program = new Command();
  program
    .requiredOption("--unkinfo <path>", "未知声明节点的 JSON 文件")
    .requiredOption("--sourcedir <dir>", "Erased 源码目录")
    .option("--output <path>", "反馈输出路径", "output/feedback.json")
    .option("--api-key <key>", "API Key (或设环境变量 DEEPSEEK_API_KEY)");
  program.parse(process.argv);

  const opts = program.opts();
  const apiKey = opts.apiKey || process.env.DEEPSEEK_API_KEY;
  if (!apiKey) {
    console.error("请设置 DEEPSEEK_API_KEY 或通过 --api-key 传入");
    process.exit(1);
  }

  const unkSpots: UnkSpot[] = JSON.parse(
    fs.readFileSync(opts.unkinfo, "utf8")
  );
  console.log(`读取 ${unkSpots.length} 个节点`);

  const sourceDir = path.resolve(opts.sourcedir);

  const feedback = await inferTypes(
    unkSpots,
    apiKey,
    30,
    (file, done, total) => {
      if (done >= total) console.log(`  ${file}: ${done}/${total}`);
    }
  );

  const outDir = path.dirname(opts.output);
  fs.mkdirSync(outDir, { recursive: true });
  fs.writeFileSync(opts.output, JSON.stringify(feedback, null, 2));
  console.log(`输出: ${feedback.length}/${unkSpots.length} 条 → ${opts.output}`);
}

main().catch((e) => {
  console.error("Agent 错误:", e.message);
  process.exit(1);
});
