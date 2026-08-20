import ts from "typescript";
import type { TypeGraph, TypeGraphNode } from "./contracts";

type FullType = Record<string, unknown>;

export interface FunctionTarget {
  id: number;
  file: string;
  line: number;
  column: number;
  name: string;
  parameterTypes: string[];
  returnType: string;
}

export interface TargetStats {
  typegraphNodes: number;
  functionNodes: number;
  canonicalTargets: number;
  ignoredNoncanonical: number;
  ignoredDuplicateCanonical: number;
  ignoredMalformed: number;
}

export function parseFullType(value: unknown): FullType | undefined {
  if (value && typeof value === "object" && !Array.isArray(value)) return value as FullType;
  if (typeof value !== "string") return undefined;
  try {
    const parsed = JSON.parse(value);
    return parsed && typeof parsed === "object" && !Array.isArray(parsed)
      ? parsed as FullType
      : undefined;
  } catch {
    return undefined;
  }
}

export function validType(typeText: string): boolean {
  if (!typeText.trim()) return false;
  if (/^(?:asserts\s+)?[A-Za-z_$][\w$]*\s+is\s+.+$/.test(typeText.trim())) return true;
  const source = ts.createSourceFile(
    "__ast2type_type.ts",
    `type __Ast2TypeProbe = ${typeText};`,
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.TS,
  );
  return (source as ts.SourceFile & { parseDiagnostics: readonly ts.Diagnostic[] })
    .parseDiagnostics.length === 0;
}

function namedType(value: string): string {
  if (value === "undefined") return "undefined";
  if (value === "unknown") return "unknown";
  if (value === "PromiseConstructor") return "Promise<any>";
  if (!value || /^obj_\d+$/.test(value) || /^new\s*(?:\(|\s)/.test(value)
    || /\)\s*:\s+\w/.test(value) || !validType(value)) return "any";
  return value;
}

function renderPropertyName(value: string): string {
  return /^[A-Za-z_$][\w$]*$/.test(value) ? value : JSON.stringify(value);
}

export function renderType(value: unknown, stripUndefined = false): string {
  if (typeof value === "string") return namedType(value);
  const type = parseFullType(value);
  if (!type) return "any";

  switch (type.kind) {
    case "primitive":
      return namedType(typeof type.name === "string" ? type.name : "unknown");
    case "literal": {
      const literal = type.value;
      if (type.valueKind === "bigint" && typeof literal === "string") {
        return /^(?:\d+|0[xX][\da-fA-F]+|0[bB][01]+|0[oO][0-7]+)n$/.test(literal)
          ? literal
          : "bigint";
      }
      if (literal === null) return "null";
      if (typeof literal === "boolean" || typeof literal === "number") return String(literal);
      if (typeof literal === "string") return /^`[\s\S]*`$/.test(literal) ? "string" : JSON.stringify(literal);
      return "any";
    }
    case "union": {
      const parts = Array.isArray(type.types)
        ? type.types
          .filter(member => !stripUndefined || !(typeof member === "string" && member === "undefined"))
          .map(member => renderType(member, stripUndefined))
        : [];
      return parts.length ? [...new Set(parts)].join(" | ") : "undefined";
    }
    case "object": {
      if (type.properties && typeof type.properties === "object" && !Array.isArray(type.properties)) {
        const members = Object.entries(type.properties as Record<string, unknown>)
          .map(([name, member]) => `${renderPropertyName(name)}: ${renderType(member)}`);
        if (members.length) return `{ ${members.join("; ")} }`;
      }
      const name = typeof type.name === "string" ? type.name : "object";
      if (/^(?:asserts\s+)?[A-Za-z_$][\w$]*\s+is\s+.+$/.test(name)) return name;
      return !name || name === "object" || /^obj_\d+$/.test(name) ? "any" : namedType(name);
    }
    case "function": {
      const parameters = Array.isArray(type.params) ? type.params : [];
      const rendered = parameters.map((parameter, index) => {
        const item = parameter && typeof parameter === "object" ? parameter as FullType : {};
        const name = typeof item.name === "string" && item.name ? item.name : `arg${index}`;
        return `${name}: ${renderType(item.type, true)}`;
      });
      return `(${rendered.join(", ")}) => ${renderType(type.returnType ?? { kind: "primitive", name: "void" })}`;
    }
    case "array": {
      const element = renderType(type.elementType);
      return /=>/.test(element) || /\s[|&]\s/.test(element) ? `(${element})[]` : `${element}[]`;
    }
    default:
      return "any";
  }
}

export function canonicalFunctionTargets(typegraph: TypeGraph): { targets: FunctionTarget[]; stats: TargetStats } {
  const stats: TargetStats = {
    typegraphNodes: Array.isArray(typegraph.nodes) ? typegraph.nodes.length : 0,
    functionNodes: 0,
    canonicalTargets: 0,
    ignoredNoncanonical: 0,
    ignoredDuplicateCanonical: 0,
    ignoredMalformed: 0,
  };
  const targets: FunctionTarget[] = [];
  const seen = new Set<string>();

  for (const node of typegraph.nodes ?? []) {
    const fullType = parseFullType(node.fullType);
    if (fullType?.kind !== "function") continue;
    stats.functionNodes++;
    const fullTypeId = fullType.id;
    if (!Number.isInteger(node.id) || !Number.isInteger(fullTypeId)) {
      stats.ignoredMalformed++;
      continue;
    }
    if (node.id !== fullTypeId) {
      stats.ignoredNoncanonical++;
      continue;
    }
    const file = typeof node.file === "string" ? node.file : "";
    const key = `${file}\0${node.id}`;
    if (seen.has(key)) {
      stats.ignoredDuplicateCanonical++;
      continue;
    }
    const start = node.position?.start;
    if (!file || !start || !Number.isInteger(start.line) || !Number.isInteger(start.character)) {
      stats.ignoredMalformed++;
      continue;
    }
    seen.add(key);
    const parameters = Array.isArray(fullType.params) ? fullType.params : [];
    targets.push({
      id: node.id,
      file,
      line: start.line,
      column: start.character,
      name: typeof fullType.name === "string" ? fullType.name : "",
      parameterTypes: parameters.map(parameter => {
        const item = parameter && typeof parameter === "object" ? parameter as FullType : {};
        return renderType(item.type, true);
      }),
      // TypeWeaver's function-signature comparator treats optional/default
      // return paths as the declared value type; omit only an undefined member
      // from the rendered return union, while preserving explicit unions in
      // standalone values.
      returnType: renderType(fullType.returnType, true),
    });
  }
  targets.sort((left, right) => left.file.localeCompare(right.file) || left.id - right.id);
  stats.canonicalTargets = targets.length;
  return { targets, stats };
}
