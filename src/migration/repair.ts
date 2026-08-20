import * as fs from "fs";
import * as path from "path";
import ts from "typescript";
import { chat, supportsOpenAIStructuredOutput } from "../../agent/net";
import type { AgentConfig } from "../../agent/net";
import type { CompileResult, Diagnostic, TextEdit } from "./contracts";
import { checkFiles, checkProject, UNIFORM_COMPILER_OPTIONS } from "./compiler";
import { applyTextEdits, discoverTypeScriptFiles, readSource, writeSource } from "./files";

export type RepairStrategy = "rules" | "agent" | "rules+agent";

export interface RepairRound {
  strategy: "rules" | "agent";
  before: number;
  after: number;
  proposed: number;
  accepted: number;
  rejected: number;
  error?: string;
}

export interface RepairResult {
  status: CompileResult["status"];
  initialDiagnostics: number;
  finalDiagnostics: number;
  acceptedEdits: number;
  rounds: RepairRound[];
  diagnostics: Diagnostic[];
}

export interface RepairOptions {
  root: string;
  contract?: "uniform" | "project";
  config?: string;
  strategy?: RepairStrategy;
  maxRuleRounds?: number;
  maxAgentRounds?: number;
  maxDiagnostics?: number;
  agent?: AgentConfig;
  agentTimeoutMs?: number;
}

type EditableDeclaration = ts.ParameterDeclaration | ts.VariableDeclaration
  | ts.PropertyDeclaration | ts.PropertySignature | ts.BindingElement;

function findAncestor<T extends ts.Node>(node: ts.Node | undefined, predicate: (value: ts.Node) => value is T): T | undefined {
  for (let current = node; current; current = current.parent) {
    if (predicate(current)) return current;
  }
  return undefined;
}

function isEditableDeclaration(node: ts.Node): node is EditableDeclaration {
  return ts.isParameter(node) || ts.isVariableDeclaration(node)
    || ts.isPropertyDeclaration(node) || ts.isPropertySignature(node)
    || ts.isBindingElement(node);
}

function leftmostIdentifier(expression: ts.Expression): ts.Identifier | undefined {
  let current: ts.Expression = expression;
  while (true) {
    if (ts.isIdentifier(current)) return current;
    if (ts.isPropertyAccessExpression(current) || ts.isElementAccessExpression(current)) {
      current = current.expression;
    } else if (ts.isParenthesizedExpression(current) || ts.isAsExpression(current)
      || ts.isTypeAssertionExpression(current) || ts.isNonNullExpression(current)) {
      current = current.expression;
    } else {
      return undefined;
    }
  }
}

function bareArrowParameter(parameter: ts.ParameterDeclaration, source: ts.SourceFile): boolean {
  return ts.isArrowFunction(parameter.parent) && parameter.parent.parameters.length === 1
    && ts.isIdentifier(parameter.name)
    && !parameter.parent.getChildren(source).some(child => child.kind === ts.SyntaxKind.OpenParenToken);
}

function bindingOwner(node: ts.BindingElement): ts.ParameterDeclaration | ts.VariableDeclaration | undefined {
  for (let current: ts.Node | undefined = node; current; current = current.parent) {
    if (ts.isParameter(current) || ts.isVariableDeclaration(current)) return current;
  }
  return undefined;
}

function inForLoop(declaration: ts.VariableDeclaration): boolean {
  const statement = declaration.parent.parent;
  return ts.isForOfStatement(statement) || ts.isForInStatement(statement);
}

function tokenAt(source: ts.SourceFile, position: number): ts.Node {
  let current: ts.Node = source;
  while (true) {
    const child = current.getChildren(source)
      .find(item => item.getFullStart() <= position && position < item.getEnd());
    if (!child) return current;
    current = child;
  }
}

function locateRuleEdits(files: string[], diagnostics: Diagnostic[]): TextEdit[] {
  const editable = new Set(files.map(file => path.resolve(file)));
  const program = ts.createProgram(files, { ...UNIFORM_COMPILER_OPTIONS, declaration: false, noEmit: true });
  const checker = program.getTypeChecker();
  const edits: TextEdit[] = [];
  const keys = new Set<string>();

  const add = (file: string, start: number, end: number, text: string): TextEdit | undefined => {
    const edit = { file: path.resolve(file), start, end, text };
    const key = `${edit.file}:${start}:${end}:${text}`;
    if (keys.has(key)) return edit;
    if (edits.some(existing => existing.file === edit.file
      && Math.max(existing.start, start) < Math.min(existing.end, end))) return undefined;
    keys.add(key);
    edits.push(edit);
    return edit;
  };

  const declarationFor = (identifier: ts.Identifier): EditableDeclaration | undefined => {
    const symbol = checker.getSymbolAtLocation(identifier);
    if (!symbol || symbol.flags & ts.SymbolFlags.Alias) return undefined;
    return [symbol.valueDeclaration, ...(symbol.declarations ?? [])]
      .find((node): node is EditableDeclaration => Boolean(node)
        && isEditableDeclaration(node!)
        && editable.has(path.resolve(node!.getSourceFile().fileName)));
  };

  const editDeclaration = (declaration: EditableDeclaration, allowInsertion: boolean): TextEdit | undefined => {
    const owner = ts.isBindingElement(declaration) ? bindingOwner(declaration) : declaration;
    if (!owner || !editable.has(path.resolve(owner.getSourceFile().fileName))) return undefined;
    if (owner.type) return add(owner.getSourceFile().fileName, owner.type.getStart(), owner.type.getEnd(), "any");
    if (!allowInsertion || !owner.name || (ts.isVariableDeclaration(owner) && inForLoop(owner))) return undefined;
    const source = owner.getSourceFile();
    const type = ts.isParameter(owner) && owner.dotDotDotToken ? "any[]" : "any";
    if (ts.isParameter(owner) && bareArrowParameter(owner, source)) {
      return add(source.fileName, owner.name.getStart(), owner.name.getEnd(), `(${owner.name.getText(source)}: ${type})`);
    }
    const position = ("questionToken" in owner ? owner.questionToken?.getEnd() : undefined)
      ?? ("exclamationToken" in owner ? owner.exclamationToken?.getEnd() : undefined)
      ?? owner.name.getEnd();
    return add(source.fileName, position, position, `: ${type}`);
  };

  const editIdentifier = (identifier: ts.Identifier | undefined, allowInsertion = true): TextEdit | undefined => {
    const declaration = identifier ? declarationFor(identifier) : undefined;
    return declaration ? editDeclaration(declaration, allowInsertion) : undefined;
  };

  const assignmentMismatch = (token: ts.Node): TextEdit | undefined => {
    for (let current: ts.Node | undefined = token; current; current = current.parent) {
      if (isEditableDeclaration(current) && "type" in current && current.type) return editDeclaration(current, false);
      if (ts.isFunctionLike(current) && current.type) {
        return add(current.getSourceFile().fileName, current.type.getStart(), current.type.getEnd(), "any");
      }
      if (ts.isReturnStatement(current)) {
        const callable = findAncestor(current.parent, ts.isFunctionLike);
        if (callable?.type) return add(callable.getSourceFile().fileName, callable.type.getStart(), callable.type.getEnd(), "any");
      }
      if (ts.isBinaryExpression(current) && current.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
        return editIdentifier(leftmostIdentifier(current.left), false);
      }
    }
    return undefined;
  };

  for (const diagnostic of diagnostics) {
    if (!diagnostic.file || diagnostic.start === undefined) continue;
    const file = path.resolve(diagnostic.file);
    const source = program.getSourceFile(file);
    if (!source || !editable.has(file)) continue;
    const token = tokenAt(source, diagnostic.start);
    if (diagnostic.code === 7006) {
      const parameter = findAncestor(token, ts.isParameter);
      if (parameter) editDeclaration(parameter, true);
    } else if (diagnostic.code === 2322) {
      assignmentMismatch(token);
    } else if (diagnostic.code === 2339) {
      const access = findAncestor(token, ts.isPropertyAccessExpression);
      if (access) editIdentifier(leftmostIdentifier(access.expression));
    } else if (diagnostic.code === 2358) {
      const binary = findAncestor(token, (node): node is ts.BinaryExpression =>
        ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword);
      if (binary) editIdentifier(leftmostIdentifier(binary.left));
    } else if (diagnostic.code === 2538) {
      const access = findAncestor(token, ts.isElementAccessExpression);
      const argument = access?.argumentExpression;
      if (argument) editIdentifier(ts.isIdentifier(argument) ? argument : ts.isIdentifier(token) ? token : undefined);
    } else if (diagnostic.code === 2571 && ts.isIdentifier(token)) {
      editIdentifier(token);
    }
  }
  return edits.sort((left, right) => left.file.localeCompare(right.file) || left.start - right.start);
}

const FIXABLE_CODES = new Set([2339, 2322, 2345, 2554, 7006, 7053, 2531, 2532, 2741, 2739, 2769, 18047, 18048]);
const SYNTAX_CODES = new Set([1002, 1003, 1005, 1009, 1010, 1109, 1128, 1136, 1160, 1161, 1185, 1434]);
const ENVIRONMENT_CODES = new Set([2307, 2304, 2688, 6053]);

function repairable(diagnostic: Diagnostic): boolean {
  return FIXABLE_CODES.has(diagnostic.code)
    || (diagnostic.code === 2552 && diagnostic.message.includes("Cannot find name 'function'"));
}

function improved(before: Diagnostic[], after: Diagnostic[]): boolean {
  const count = (items: Diagnostic[], codes: Set<number>) => items.filter(item => codes.has(item.code)).length;
  return count(after, SYNTAX_CODES) <= count(before, SYNTAX_CODES)
    && count(after, ENVIRONMENT_CODES) <= count(before, ENVIRONMENT_CODES)
    && after.length < before.length;
}

interface AgentEdit {
  file: string;
  before: string;
  after: string;
  reason: string;
}

const REPAIR_SCHEMA: Record<string, unknown> = {
  type: "object",
  properties: {
    edits: {
      type: "array",
      items: {
        type: "object",
        properties: {
          file: { type: "string" }, before: { type: "string" },
          after: { type: "string" }, reason: { type: "string" },
        },
        required: ["file", "before", "after", "reason"],
        additionalProperties: false,
      },
    },
    skip: {
      type: "array",
      items: {
        type: "object",
        properties: {
          file: { type: "string" },
          reason: { type: "string" },
        },
        required: ["file", "reason"],
        additionalProperties: false,
      },
    },
  },
  required: ["edits", "skip"],
  additionalProperties: false,
};

function sourceContext(file: string, diagnostics: Diagnostic[]): string {
  const lines = readSource(file).split(/\r?\n/);
  const selected = new Set<number>();
  for (const diagnostic of diagnostics) {
    if (!diagnostic.line) continue;
    for (let line = Math.max(1, diagnostic.line - 12); line <= Math.min(lines.length, diagnostic.line + 12); line++) {
      selected.add(line);
    }
  }
  return [...selected].sort((a, b) => a - b).map(line => `${String(line).padStart(5)} | ${lines[line - 1]}`).join("\n");
}

function agentPrompt(round: number, diagnostics: Diagnostic[]): string {
  const byFile = new Map<string, Diagnostic[]>();
  for (const diagnostic of diagnostics) {
    if (!diagnostic.file) continue;
    const group = byFile.get(diagnostic.file) ?? [];
    group.push(diagnostic);
    byFile.set(diagnostic.file, group);
  }
  const files = [...byFile].map(([file, items]) => `## File: ${file}\n### Diagnostics\n${items
    .map(item => `TS${item.code} at ${item.line}:${item.column}: ${item.message}`).join("\n")}
### Context\n\`\`\`typescript\n${sourceContext(file, items)}\n\`\`\``).join("\n\n");
  return `Repair generated TypeScript using the compiler diagnostics below. This is round ${round}.

${files}

Return only JSON: {"edits":[{"file":"...","before":"exact text","after":"replacement","reason":"..."}],"skip":[]}.
- Make small local changes only.
- Prefer a type annotation, an as-any cast, or widening a callback signature.
- For callback arity errors, preserve parameters used by the callback body.
- Replace an invalid generated annotation such as : function with : any.
- before must be an exact single-line source substring and identify one occurrence.
- Do not add dependencies, rewrite business logic, or edit unlisted files.`;
}

function responseJson(content: string): unknown {
  const trimmed = content.trim();
  // Some providers omit the closing Markdown fence even when the JSON itself is complete.
  const fenced = trimmed.match(/```(?:json)?\s*([\s\S]*?)(?:\s*```|$)/i);
  return JSON.parse(fenced ? fenced[1].trim() : trimmed);
}

function agentEdits(value: unknown): AgentEdit[] {
  const document = Array.isArray(value) ? { edits: value } : value;
  if (!document || typeof document !== "object") return [];
  const raw = (document as Record<string, unknown>).edits;
  if (!Array.isArray(raw)) return [];
  return raw.flatMap(item => {
    if (!item || typeof item !== "object") return [];
    const edit = item as Record<string, unknown>;
    const before = edit.before ?? edit.old_text ?? edit.old;
    const after = edit.after ?? edit.new_text ?? edit.new ?? edit.replacement;
    return typeof edit.file === "string" && typeof before === "string" && before.trim()
      && typeof after === "string" && !/[\r\n]/.test(before) && !/[\r\n]/.test(after)
      ? [{ file: edit.file, before, after, reason: typeof edit.reason === "string" ? edit.reason : "" }]
      : [];
  });
}

async function requestAgent(config: AgentConfig, round: number, diagnostics: Diagnostic[], timeoutMs: number): Promise<AgentEdit[]> {
  const structured = config.provider === "openai" && supportsOpenAIStructuredOutput(config.model);
  const response = await chat(config, {
    messages: [{ role: "user", content: agentPrompt(round, diagnostics) }],
    structuredOutput: structured ? { name: "ts_repair", schema: REPAIR_SCHEMA } : undefined,
    timeoutMs,
  });
  return agentEdits(responseJson(response.content));
}

function resolveAgentFile(root: string, requested: string, files: string[]): string | undefined {
  const direct = path.resolve(requested);
  if (files.includes(direct)) return direct;
  const suffix = requested.replace(/^\.\//, "").split(/[\\/]/).join(path.sep);
  const matches = files.filter(file => file.endsWith(`${path.sep}${suffix}`));
  return matches.length === 1 ? matches[0] : undefined;
}

export async function repairProject(options: RepairOptions): Promise<RepairResult> {
  const root = path.resolve(options.root);
  const files = discoverTypeScriptFiles(root);
  const compile = (): CompileResult => options.contract === "project"
    ? checkProject({ root, config: options.config })
    : checkFiles({ files });
  let current = compile();
  const initialDiagnostics = current.diagnostics.length;
  const rounds: RepairRound[] = [];
  let acceptedEdits = 0;
  const strategy = options.strategy ?? "rules";

  if (strategy === "rules" || strategy === "rules+agent") {
    for (let round = 0; round < (options.maxRuleRounds ?? 5) && current.status === "type-error"; round++) {
      const before = current.diagnostics;
      const edits = locateRuleEdits(files, before);
      if (!edits.length) break;
      const snapshots = new Map([...new Set(edits.map(edit => edit.file))].map(file => [file, readSource(file)]));
      applyTextEdits(root, edits, files);
      const candidate = compile();
      if (candidate.status !== "tool-error" && improved(before, candidate.diagnostics)) {
        current = candidate;
        acceptedEdits += edits.length;
        rounds.push({ strategy: "rules", before: before.length, after: current.diagnostics.length, proposed: edits.length, accepted: edits.length, rejected: 0 });
      } else {
        for (const [file, content] of snapshots) writeSource(file, content);
        rounds.push({ strategy: "rules", before: before.length, after: before.length, proposed: edits.length, accepted: 0, rejected: edits.length });
        break;
      }
    }
  }

  if (strategy === "agent" || strategy === "rules+agent") {
    if (!options.agent) throw new Error("agent repair requires an agent configuration");
    for (let round = 1; round <= (options.maxAgentRounds ?? 2) && current.status === "type-error"; round++) {
      let diagnostics = current.diagnostics.filter(repairable).slice(0, options.maxDiagnostics ?? 10);
      if (!diagnostics.length) break;
      let proposed: AgentEdit[];
      try {
        proposed = await requestAgent(options.agent, round, diagnostics, options.agentTimeoutMs ?? 90_000);
      } catch (error) {
        // A malformed/truncated response must not discard the compilable input project.
        rounds.push({
          strategy: "agent",
          before: current.diagnostics.length,
          after: current.diagnostics.length,
          proposed: 0,
          accepted: 0,
          rejected: 0,
          error: error instanceof Error ? error.message : String(error),
        });
        break;
      }
      let accepted = 0;
      let rejected = 0;
      const beforeRound = current.diagnostics.length;
      for (const proposal of proposed) {
        const file = resolveAgentFile(root, proposal.file, files);
        if (!file) { rejected++; continue; }
        const content = readSource(file);
        if (content.split(proposal.before).length !== 2) { rejected++; continue; }
        const start = content.indexOf(proposal.before);
        applyTextEdits(root, [{ file, start, end: start + proposal.before.length, text: proposal.after }], files);
        const candidate = compile();
        if (candidate.status !== "tool-error" && improved(current.diagnostics, candidate.diagnostics)) {
          current = candidate;
          diagnostics = current.diagnostics;
          accepted++;
          acceptedEdits++;
        } else {
          writeSource(file, content);
          rejected++;
        }
      }
      rounds.push({ strategy: "agent", before: beforeRound, after: current.diagnostics.length, proposed: proposed.length, accepted, rejected });
      if (!accepted) break;
    }
  }

  return {
    status: current.status,
    initialDiagnostics,
    finalDiagnostics: current.diagnostics.length,
    acceptedEdits,
    rounds,
    diagnostics: current.diagnostics,
  };
}
