import * as fs from "fs";
import * as path from "path";
import { spawnSync } from "child_process";
import type { TypeGraph } from "../migration/contracts";
import { pathsOverlap } from "../migration/files";

export type InferenceMode = "std" | "agent";
export type AgentCandidateMode = "fair" | "gt";

export interface InferenceOptions {
  source: string;
  output: string;
  jsOnly?: boolean;
  mode?: InferenceMode;
  candidateMode?: AgentCandidateMode;
  refineAny?: boolean;
  signatureOnly?: boolean;
  agentBatchSize?: number;
  agentConsensusRounds?: number;
  agentConcurrency?: number;
  provider?: string;
  model?: string;
  baseUrl?: string;
  timeoutMs?: number;
}

export interface InferenceResult {
  output: string;
  typegraph: TypeGraph;
}

const PROJECT_ROOT = path.resolve(__dirname, "../..");

function run(entrypoint: string, args: string[], timeoutMs: number): void {
  const result = spawnSync(
    process.execPath,
    ["--max-old-space-size=40960", "-r", "ts-node/register", entrypoint, ...args],
    { cwd: PROJECT_ROOT, stdio: "inherit", timeout: timeoutMs },
  );
  if (result.error) throw result.error;
  if (result.status !== 0) {
    throw new Error(`${path.basename(entrypoint)} exited with status ${result.status}`);
  }
}

/** Run the existing inference engine behind one stable programmatic boundary. */
export function inferProject(options: InferenceOptions): InferenceResult {
  const source = path.resolve(options.source);
  const output = path.resolve(options.output);
  const mode = options.mode ?? "std";
  const timeoutMs = options.timeoutMs ?? 600_000;
  if (!fs.existsSync(source) || !fs.statSync(source).isDirectory()) {
    throw new Error(`source is not a directory: ${source}`);
  }
  if (pathsOverlap(source, output)) throw new Error("source and inference output must not overlap");
  if (fs.existsSync(output)) fs.rmSync(output, { recursive: true, force: true });
  fs.mkdirSync(output, { recursive: true });

  const astArgs = ["-i", source, "-o", output];
  if (options.jsOnly) astArgs.push("--js-only");
  run(path.join(PROJECT_ROOT, "code2ast.ts"), astArgs, timeoutMs);
  const args = ["-i", path.join(output, "ast"), "-o", output, "--sourcedir", source];
  if (mode === "agent") {
    args.push("--agent", "--agent-candidate-mode", options.candidateMode ?? "fair");
    if (options.refineAny) args.push("--agent-refine-any");
    if (options.signatureOnly) args.push("--agent-signature-only");
    if (options.agentBatchSize !== undefined) args.push("--agent-batch-size", String(options.agentBatchSize));
    if (options.agentConsensusRounds !== undefined) args.push("--agent-consensus-rounds", String(options.agentConsensusRounds));
    if (options.agentConcurrency !== undefined) args.push("--agent-concurrency", String(options.agentConcurrency));
    if (options.provider) args.push("--agent-provider", options.provider);
    if (options.model) args.push("--agent-model", options.model);
    if (options.baseUrl) args.push("--agent-base-url", options.baseUrl);
  }
  run(path.join(PROJECT_ROOT, "ast2type.ts"), args, timeoutMs);

  const typegraphPath = path.join(output, "typegraph.json");
  if (!fs.existsSync(typegraphPath)) throw new Error(`inference did not produce ${typegraphPath}`);
  return {
    output,
    typegraph: JSON.parse(fs.readFileSync(typegraphPath, "utf8")) as TypeGraph,
  };
}

export function inferJavaScript(options: InferenceOptions): InferenceResult {
  return inferProject({ ...options, jsOnly: true });
}
