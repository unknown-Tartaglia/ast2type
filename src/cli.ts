#!/usr/bin/env node
import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";
import { getAgentApiKeyEnvName, resolveAgentConfig } from "../agent/net";
import type { GroundTruth, TypeGraph } from "./migration/contracts";
import { checkDirectory, checkProject } from "./migration/compiler";
import { pathsOverlap } from "./migration/files";
import { weaveJavaScript, writeJavaScriptMigration } from "./migration/js";
import { migrateJavaScriptProject, migrateTypeScriptProject } from "./migration/project";
import { repairProject } from "./migration/repair";
import type { RepairStrategy } from "./migration/repair";
import { eraseTypeScript, restoreTypeScript } from "./migration/ts";

function jsonFile<T>(file: string): T {
  return JSON.parse(fs.readFileSync(path.resolve(file), "utf8")) as T;
}

function print(value: unknown): void {
  process.stdout.write(`${JSON.stringify(value, null, 2)}\n`);
}

function statusCode(status: string): number {
  return status === "pass" ? 0 : status === "type-error" ? 1 : 2;
}

function copyProject(source: string, output: string): string {
  const input = path.resolve(source);
  const target = path.resolve(output);
  if (fs.existsSync(target)) throw new Error(`output directory already exists: ${target}`);
  if (pathsOverlap(input, target)) throw new Error("source and output directory must not overlap");
  fs.cpSync(input, target, {
    recursive: true,
    filter: value => !["node_modules", ".git"].includes(path.basename(value)),
  });
  return target;
}

const program = new Command("ast2type")
  .description("Type inference, migration, compilation, and repair");

program.command("weave-js")
  .argument("<source>", "JavaScript project")
  .requiredOption("--typegraph <file>")
  .requiredOption("--out <directory>")
  .action((source, options) => {
    const woven = weaveJavaScript(source, jsonFile<TypeGraph>(options.typegraph));
    writeJavaScriptMigration(options.out, woven);
    print(woven.report);
  });

program.command("migrate-js")
  .argument("<source>", "JavaScript project")
  .requiredOption("--out <directory>")
  .requiredOption("--work-dir <directory>", "isolated inference artifacts")
  .option("--mode <mode>", "std or agent", "std")
  .option("--candidate-mode <mode>", "fair or gt", "fair")
  .option("--agent-provider <provider>")
  .option("--agent-model <model>")
  .option("--agent-base-url <url>")
  .option("--timeout <seconds>", "inference timeout", "600")
  .option("--keep-work-dir")
  .action((source, options) => {
    if (!["std", "agent"].includes(options.mode)) throw new Error("mode must be std or agent");
    if (!["fair", "gt"].includes(options.candidateMode)) throw new Error("candidate mode must be fair or gt");
    if (options.mode === "std" && (options.agentProvider || options.agentModel || options.agentBaseUrl)) {
      throw new Error("agent options require --mode agent");
    }
    print(migrateJavaScriptProject({
      source,
      output: options.out,
      workDirectory: options.workDir,
      mode: options.mode,
      candidateMode: options.candidateMode,
      provider: options.agentProvider,
      model: options.agentModel,
      baseUrl: options.agentBaseUrl,
      timeoutMs: Number(options.timeout) * 1000,
      keepWorkDirectory: Boolean(options.keepWorkDir),
    }));
  });

program.command("erase-ts")
  .argument("<source>", "TypeScript project")
  .requiredOption("--out <directory>")
  .action((source, options) => print(eraseTypeScript(source, options.out)));

program.command("migrate-ts")
  .argument("<source>", "TypeScript project")
  .requiredOption("--out <directory>")
  .requiredOption("--work-dir <directory>", "isolated erase and inference artifacts")
  .option("--mode <mode>", "std or agent", "std")
  .option("--candidate-mode <mode>", "fair or gt", "fair")
  .option("--agent-provider <provider>")
  .option("--agent-model <model>")
  .option("--agent-base-url <url>")
  .option("--timeout <seconds>", "inference timeout", "600")
  .option("--keep-work-dir")
  .action((source, options) => {
    if (!["std", "agent"].includes(options.mode)) throw new Error("mode must be std or agent");
    if (!["fair", "gt"].includes(options.candidateMode)) throw new Error("candidate mode must be fair or gt");
    if (options.mode === "std" && (options.agentProvider || options.agentModel || options.agentBaseUrl)) {
      throw new Error("agent options require --mode agent");
    }
    print(migrateTypeScriptProject({
      source,
      output: options.out,
      workDirectory: options.workDir,
      mode: options.mode,
      candidateMode: options.candidateMode,
      provider: options.agentProvider,
      model: options.agentModel,
      baseUrl: options.agentBaseUrl,
      timeoutMs: Number(options.timeout) * 1000,
      keepWorkDirectory: Boolean(options.keepWorkDir),
    }));
  });

program.command("restore-ts")
  .argument("<base>", "original TypeScript project")
  .requiredOption("--erased <directory>")
  .requiredOption("--groundtruth <file>")
  .requiredOption("--typegraph <file>")
  .requiredOption("--out <directory>")
  .option("--inference-source <directory>")
  .action((base, options) => print(restoreTypeScript({
    baseProject: base,
    erasedRoot: options.erased,
    outputRoot: options.out,
    groundTruth: jsonFile<GroundTruth>(options.groundtruth),
    typegraph: jsonFile<TypeGraph>(options.typegraph),
    inferenceSourceRoot: options.inferenceSource,
  })));

program.command("check")
  .argument("<project>")
  .option("--contract <contract>", "uniform or project", "uniform")
  .option("--config <file>", "project tsconfig", "tsconfig.json")
  .option("--declarations <directory>")
  .action((project, options) => {
    if (!['uniform', 'project'].includes(options.contract)) {
      throw new Error("contract must be uniform or project");
    }
    const result = options.contract === "project"
      ? checkProject({ root: project, config: options.config })
      : checkDirectory(project, options.declarations);
    print(result);
    process.exitCode = statusCode(result.status);
  });

program.command("repair")
  .argument("<project>")
  .option("--out <directory>", "copy before repairing")
  .option("--strategy <strategy>", "rules, agent, or rules+agent", "rules")
  .option("--contract <contract>", "uniform or project", "uniform")
  .option("--config <file>", "project tsconfig", "tsconfig.json")
  .option("--rule-rounds <number>", "maximum rule rounds", "5")
  .option("--agent-rounds <number>", "maximum agent rounds", "2")
  .option("--max-diagnostics <number>", "diagnostics per agent round", "10")
  .option("--agent-provider <provider>")
  .option("--agent-model <model>")
  .option("--agent-base-url <url>")
  .action(async (project, options) => {
    const strategies = new Set(["rules", "agent", "rules+agent"]);
    if (!strategies.has(options.strategy)) throw new Error("invalid repair strategy");
    if (!["uniform", "project"].includes(options.contract)) throw new Error("invalid compiler contract");
    const strategy = options.strategy as RepairStrategy;
    const root = options.out ? copyProject(project, options.out) : path.resolve(project);
    const needsAgent = strategy === "agent" || strategy === "rules+agent";
    const agent = needsAgent ? resolveAgentConfig({
      provider: options.agentProvider,
      model: options.agentModel,
      baseUrl: options.agentBaseUrl,
    }) : undefined;
    if (agent && !agent.apiKey) throw new Error(`missing ${getAgentApiKeyEnvName(agent.provider)}`);
    const result = await repairProject({
      root,
      strategy,
      contract: options.contract,
      config: options.config,
      maxRuleRounds: Number(options.ruleRounds),
      maxAgentRounds: Number(options.agentRounds),
      maxDiagnostics: Number(options.maxDiagnostics),
      agent,
    });
    print(result);
    process.exitCode = statusCode(result.status);
  });

program.parseAsync(process.argv).catch(error => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exitCode = 2;
});
