/**
 * ast2type Agent CLI - LLM 辅助类型推断（独立命令行工具）
 *
 * 用法:
 *   npx tsx agent/index.ts \
 *     --unkinfo output/agent-candidates.json \
 *     --sourcedir /path/to/erased_sources \
 *     --output output/feedback.json
 *
 * OpenAI 直连：额外传入 --agent-provider openai，并设置 OPENAI_API_KEY。
 *
 * 注：Agent 已集成到 ast2type 主流程（--agent），本 CLI 仅用于外部调试。
 */

import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";
import { inferTypes } from "./infer";
import { getAgentApiKeyEnvName, resolveAgentConfig } from "./net";
import type { AgentConfig } from "./net";
import type { UnkSpot } from "../ast2type/solver";

async function main() {
  const program = new Command();
  program
    .requiredOption("--unkinfo <path>", "Agent 候选数组或 agent-candidates.json 快照")
    .requiredOption("--sourcedir <dir>", "Erased 源码目录")
    .option("--output <path>", "反馈输出路径", "output/feedback.json")
    .option("--agent-provider <provider>", "API provider: deepseek（默认）或 openai")
    .option("--agent-model <model>", "覆盖 provider 默认模型")
    .option("--agent-base-url <url>", "覆盖 provider API base URL")
    .option("--api-key <key>", "API Key（也可设置 provider 对应的环境变量）");
  program.parse(process.argv);

  const opts = program.opts();
  let config: AgentConfig;
  try {
    config = resolveAgentConfig({
      provider: opts.agentProvider,
      model: opts.agentModel,
      baseUrl: opts.agentBaseUrl,
      apiKey: opts.apiKey,
    });
  } catch (error) {
    program.error(error instanceof Error ? error.message : String(error));
    throw error;
  }
  if (!config.apiKey) {
    const envName = getAgentApiKeyEnvName(config.provider);
    console.error(`请设置 ${envName} 或通过 --api-key 传入`);
    process.exit(1);
  }

  const candidateDocument = JSON.parse(fs.readFileSync(opts.unkinfo, "utf8"));
  const rawSpots = Array.isArray(candidateDocument)
    ? candidateDocument
    : candidateDocument.candidates;
  if (!Array.isArray(rawSpots)) {
    throw new Error("候选文件必须是数组或包含 candidates 数组的快照");
  }
  const unkSpots: UnkSpot[] = rawSpots.map((spot: Partial<UnkSpot>) => ({
    ...spot,
    slot: spot.slot ?? "value",
  })) as UnkSpot[];
  console.log(`读取 ${unkSpots.length} 个节点`);

  const sourceDir = path.resolve(opts.sourcedir);
  const sourceSpots = unkSpots.map((spot) =>
    spot.relapath === "unknown_relapath"
      ? spot
      : { ...spot, file: path.join(sourceDir, spot.relapath) }
  );

  const feedback = await inferTypes(
    sourceSpots,
    config,
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
