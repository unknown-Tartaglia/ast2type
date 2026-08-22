import * as fs from "fs";
import * as path from "path";
import { inferJavaScript, inferProject } from "../inference/runner";
import type { AgentCandidateMode, InferenceMode } from "../inference/runner";
import type { GroundTruth } from "./contracts";
import { pathsOverlap } from "./files";
import { weaveJavaScript, writeJavaScriptMigration } from "./js";
import type { WeaveReport } from "./js";
import { eraseTypeScript, restoreTypeScript } from "./ts";
import type { RestoreReport } from "./ts";

export interface MigrateJavaScriptOptions {
  source: string;
  output: string;
  workDirectory: string;
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
  keepWorkDirectory?: boolean;
}

export interface MigrationResult {
  source: string;
  output: string;
  mode: InferenceMode;
  weave: WeaveReport;
}

export interface MigrateTypeScriptOptions extends Omit<MigrateJavaScriptOptions, "keepWorkDirectory"> {
  keepWorkDirectory?: boolean;
}

export interface TypeScriptMigrationResult {
  source: string;
  output: string;
  mode: InferenceMode;
  restore: RestoreReport;
}

/** Infer and migrate one JavaScript project. Dataset batching belongs outside ast2type. */
export function migrateJavaScriptProject(options: MigrateJavaScriptOptions): MigrationResult {
  const source = path.resolve(options.source);
  const output = path.resolve(options.output);
  const workDirectory = path.resolve(options.workDirectory);
  const mode = options.mode ?? "std";
  if (fs.existsSync(output)) throw new Error(`output directory already exists: ${output}`);
  if (pathsOverlap(source, output) || pathsOverlap(source, workDirectory)
    || pathsOverlap(output, workDirectory)) {
    throw new Error("source, output, and work directory must not overlap");
  }

  try {
    const inferred = inferJavaScript({
      source,
      output: workDirectory,
      mode,
      candidateMode: options.candidateMode,
      refineAny: options.refineAny,
      signatureOnly: options.signatureOnly,
      agentBatchSize: options.agentBatchSize,
      agentConsensusRounds: options.agentConsensusRounds,
      agentConcurrency: options.agentConcurrency,
      provider: options.provider,
      model: options.model,
      baseUrl: options.baseUrl,
      timeoutMs: options.timeoutMs,
    });
    const woven = weaveJavaScript(source, inferred.typegraph);
    writeJavaScriptMigration(output, woven);
    return { source, output, mode, weave: woven.report };
  } finally {
    if (!options.keepWorkDirectory) fs.rmSync(workDirectory, { recursive: true, force: true });
  }
}

/** Erase annotations, infer from erased sources, then restore inferred annotations. */
export function migrateTypeScriptProject(options: MigrateTypeScriptOptions): TypeScriptMigrationResult {
  const source = path.resolve(options.source);
  const output = path.resolve(options.output);
  const workDirectory = path.resolve(options.workDirectory);
  const erased = path.join(workDirectory, "erased");
  const inference = path.join(workDirectory, "inference");
  const mode = options.mode ?? "std";
  if (fs.existsSync(output)) throw new Error(`output directory already exists: ${output}`);
  if (pathsOverlap(source, output) || pathsOverlap(source, workDirectory)
    || pathsOverlap(output, workDirectory)) {
    throw new Error("source, output, and work directory must not overlap");
  }

  if (fs.existsSync(workDirectory)) fs.rmSync(workDirectory, { recursive: true, force: true });
  try {
    eraseTypeScript(source, erased);
    const inferred = inferProject({
      source: erased,
      output: inference,
      mode,
      candidateMode: options.candidateMode,
      refineAny: options.refineAny,
      signatureOnly: options.signatureOnly,
      agentBatchSize: options.agentBatchSize,
      agentConsensusRounds: options.agentConsensusRounds,
      agentConcurrency: options.agentConcurrency,
      provider: options.provider,
      model: options.model,
      baseUrl: options.baseUrl,
      timeoutMs: options.timeoutMs,
    });
    const groundTruthPath = path.join(erased, "_groundtruth.json");
    const groundTruth = JSON.parse(fs.readFileSync(groundTruthPath, "utf8")) as GroundTruth;
    const restore = restoreTypeScript({
      baseProject: source,
      erasedRoot: erased,
      outputRoot: output,
      groundTruth,
      typegraph: inferred.typegraph,
      inferenceSourceRoot: erased,
    });
    return { source, output, mode, restore };
  } finally {
    if (!options.keepWorkDirectory) fs.rmSync(workDirectory, { recursive: true, force: true });
  }
}
