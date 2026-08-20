import * as fs from "fs";
import * as path from "path";
import ts from "typescript";
import type {
  AnnotationEntry,
  AnnotationKind,
  GroundTruth,
  TextEdit,
  TypeGraph,
  TypeGraphNode,
} from "./contracts";
import { applyEditsToText, readSource, resolveInside, writeSource } from "./files";
import { parseFullType, renderType } from "./typegraph";

const TS_EXTENSIONS = new Set([".ts", ".tsx", ".mts", ".cts", ".ets"]);
const DECLARATION_PATTERN = /\.d\.(?:ts|mts|cts|ets)$/;
const IGNORED_DIRECTORIES = new Set(["node_modules", ".git"]);

export interface EraseResult {
  files: number;
  annotations: number;
  annotatedFiles: number;
  groundTruth: GroundTruth;
}

export interface RestoreReport {
  annotations: number;
  inferred: number;
  unannotated: number;
  syntaxFallback: number;
  files: number;
  invalidSpans: Array<{ file: string; identifier?: string; reason: string }>;
}

function sourceFiles(root: string): string[] {
  const files: string[] = [];
  const visit = (directory: string): void => {
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })
      .sort((left, right) => left.name.localeCompare(right.name))) {
      const target = path.join(directory, entry.name);
      if (entry.isDirectory()) {
        if (!IGNORED_DIRECTORIES.has(entry.name)) visit(target);
      } else if (entry.isFile() && TS_EXTENSIONS.has(path.extname(entry.name).toLowerCase())) {
        files.push(path.resolve(target));
      }
    }
  };
  visit(root);
  return files;
}

function scriptKind(file: string): ts.ScriptKind {
  if (/\.tsx$/i.test(file)) return ts.ScriptKind.TSX;
  return ts.ScriptKind.TS;
}

function identity(node: ts.NamedDeclaration): { node: ts.Node; inferable: boolean; matchText: boolean } {
  const name = node.name;
  if (!name) return { node, inferable: true, matchText: false };
  return ts.isIdentifier(name)
    ? { node: name, inferable: true, matchText: true }
    : { node: name, inferable: false, matchText: false };
}

function functionIdentity(node: ts.SignatureDeclaration): { node: ts.Node; inferable: boolean; matchText: boolean } {
  return "name" in node && node.name ? identity(node as ts.NamedDeclaration) : {
    node,
    inferable: true,
    matchText: false,
  };
}

function annotationStart(content: string, typeStart: number): number | undefined {
  for (let index = typeStart - 1; index >= 0 && /\s/.test(content[index]); index--) {
    if (content[index] === ":") return index;
  }
  let index = typeStart - 1;
  while (index >= 0 && /\s/.test(content[index])) index--;
  return content[index] === ":" ? index : undefined;
}

function collectAnnotations(source: ts.SourceFile): AnnotationEntry[] {
  const content = source.getFullText();
  const annotations: AnnotationEntry[] = [];
  const record = (
    type: ts.TypeNode | undefined,
    target: { node: ts.Node; inferable: boolean; matchText: boolean },
    kind: AnnotationKind,
    isAsync = false,
  ): void => {
    if (!type) return;
    const start = annotationStart(content, type.getStart(source));
    if (start === undefined) return;
    const location = source.getLineAndCharacterOfPosition(target.node.getStart(source));
    annotations.push({
      identifier: target.node.getText(source),
      offset: target.node.getStart(source),
      annotationStart: start,
      annotationEnd: type.getEnd(),
      line: location.line + 1,
      col: location.character + 1,
      type: type.getText(source),
      kind,
      isAsync: isAsync || undefined,
      inferable: target.inferable,
      matchText: target.matchText,
    });
  };

  const visit = (node: ts.Node): void => {
    if (ts.isParameter(node)) {
      record(node.type, identity(node), ts.isIndexSignatureDeclaration(node.parent) ? "index" : "param");
    } else if (ts.isVariableDeclaration(node)) {
      record(node.type, identity(node), "variable");
    } else if (ts.isPropertyDeclaration(node)) {
      record(node.type, identity(node), "variable");
    } else if (ts.isPropertySignature(node)) {
      record(node.type, identity(node), "property");
    } else if (ts.isIndexSignatureDeclaration(node)) {
      const key = node.parameters[0]?.name ?? node;
      record(node.type, { node: key, inferable: false, matchText: false }, "index-value");
    }

    if ((ts.isFunctionDeclaration(node) || ts.isMethodDeclaration(node)
      || ts.isMethodSignature(node) || ts.isArrowFunction(node)
      || ts.isFunctionExpression(node) || ts.isGetAccessorDeclaration(node)
      || ts.isCallSignatureDeclaration(node) || ts.isConstructSignatureDeclaration(node))
      && node.type) {
      record(
        node.type,
        functionIdentity(node),
        "return",
        ts.canHaveModifiers(node)
          && (ts.getModifiers(node)?.some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword) ?? false),
      );
    }
    ts.forEachChild(node, visit);
  };
  visit(source);

  return annotations.filter((annotation, index) => !annotations.some((outer, outerIndex) =>
    outerIndex !== index
    && outer.annotationStart <= annotation.annotationStart
    && outer.annotationEnd >= annotation.annotationEnd
    && (outer.annotationStart < annotation.annotationStart || outer.annotationEnd > annotation.annotationEnd)));
}

export function eraseTypeScript(sourceRoot: string, outputRoot: string): EraseResult {
  const source = path.resolve(sourceRoot);
  const output = path.resolve(outputRoot);
  if (fs.existsSync(output)) throw new Error(`output directory already exists: ${output}`);
  fs.mkdirSync(output, { recursive: true });
  const groundTruth: GroundTruth = {};
  let annotationCount = 0;

  const files = sourceFiles(source);
  for (const file of files) {
    const relative = path.relative(source, file);
    const content = readSource(file);
    if (DECLARATION_PATTERN.test(file)) {
      writeSource(resolveInside(output, relative), content);
      continue;
    }
    const parsed = ts.createSourceFile(file, content, ts.ScriptTarget.Latest, true, scriptKind(file));
    const annotations = collectAnnotations(parsed);
    let erased = content;
    for (const annotation of [...annotations].sort((left, right) => right.annotationStart - left.annotationStart)) {
      const segment = erased.slice(annotation.annotationStart, annotation.annotationEnd);
      erased = erased.slice(0, annotation.annotationStart)
        + segment.replace(/\S/g, " ")
        + erased.slice(annotation.annotationEnd);
    }
    writeSource(resolveInside(output, relative), erased);
    if (annotations.length) {
      groundTruth[relative] = annotations;
      annotationCount += annotations.length;
    }
  }
  writeSource(path.join(output, "_groundtruth.json"), `${JSON.stringify(groundTruth, null, 2)}\n`);
  return {
    files: files.length,
    annotations: annotationCount,
    annotatedFiles: Object.keys(groundTruth).length,
    groundTruth,
  };
}

interface Candidate {
  text: string;
  fullType: unknown;
}

function normalPath(value: string): string {
  return path.normalize(value.replace(/\^/g, path.sep).replace(/[\\/]/g, path.sep));
}

function candidateIndex(typegraph: TypeGraph, sourceRoot: string): Map<string, Candidate[]> {
  const index = new Map<string, Candidate[]>();
  const root = path.resolve(sourceRoot);
  for (const node of typegraph.nodes ?? []) {
    if (typeof node.file !== "string" || !node.position?.start || node.fullType === undefined) continue;
    let relative: string;
    try {
      relative = normalPath(path.relative(root, path.resolve(normalPath(node.file))));
      if (relative === ".." || relative.startsWith(`..${path.sep}`)) continue;
    } catch {
      continue;
    }
    const key = `${relative}\0${node.position.start.line}\0${node.position.start.character}`;
    const group = index.get(key) ?? [];
    group.push({ text: node.text ?? node.label ?? "", fullType: node.fullType });
    index.set(key, group);
  }
  return index;
}

function unknownType(value: unknown): boolean {
  if (value === "unknown") return true;
  const type = parseFullType(value);
  return type?.kind === "unknown" || (type?.kind === "primitive" && type.name === "unknown");
}

function inferredType(candidate: Candidate, annotation: AnnotationEntry): string | undefined {
  let value = candidate.fullType;
  const parsed = parseFullType(value);
  if (annotation.kind === "return") {
    if (parsed?.kind !== "function") return undefined;
    value = parsed.returnType;
  }
  if (unknownType(value)) return undefined;
  const literal = parseFullType(value);
  if (literal?.kind === "literal") {
    if (literal.valueKind === "bigint") return "bigint";
    if (typeof literal.value === "boolean") return "boolean";
    if (typeof literal.value === "number") return "number";
    if (typeof literal.value === "string") return "string";
  }
  return renderType(literal ?? value);
}

function annotationType(annotation: AnnotationEntry, candidates: Candidate[]): { type?: string; matched: boolean } {
  const exact = candidates.filter(candidate => candidate.text === annotation.identifier);
  const pool = annotation.inferable
    ? (annotation.matchText ? exact : exact.length ? exact : candidates)
    : [];
  if (annotation.kind === "index") {
    const type = pool.map(candidate => inferredType(candidate, annotation))
      .find(value => value === "string" || value === "number" || value === "symbol");
    return { type: type ?? "string", matched: Boolean(type) };
  }
  if (annotation.kind === "index-value") {
    const type = pool.map(candidate => inferredType(candidate, annotation)).find(Boolean);
    return { type: type ?? "any", matched: Boolean(type) };
  }
  if (annotation.kind === "property" && !pool.length) return { type: "any", matched: false };
  for (const candidate of pool) {
    let type = inferredType(candidate, annotation);
    if (!type) continue;
    if (annotation.kind === "return" && annotation.isAsync && !/^Promise(?:<|$)/.test(type)) {
      type = `Promise<${type}>`;
    }
    return { type, matched: true };
  }
  return { matched: false };
}

function copyProject(baseProject: string, erasedRoot: string, outputRoot: string): void {
  const output = path.resolve(outputRoot);
  if (fs.existsSync(output)) throw new Error(`output directory already exists: ${output}`);
  fs.cpSync(path.resolve(baseProject), output, {
    recursive: true,
    filter: source => !IGNORED_DIRECTORIES.has(path.basename(source)),
  });
  const erased = path.resolve(erasedRoot);
  for (const file of sourceFiles(erased)) {
    writeSource(resolveInside(output, path.relative(erased, file)), readSource(file));
  }
}

export interface RestoreOptions {
  baseProject: string;
  erasedRoot: string;
  outputRoot: string;
  groundTruth: GroundTruth;
  typegraph: TypeGraph;
  inferenceSourceRoot?: string;
}

export function restoreTypeScript(options: RestoreOptions): RestoreReport {
  copyProject(options.baseProject, options.erasedRoot, options.outputRoot);
  const output = path.resolve(options.outputRoot);
  const candidates = candidateIndex(options.typegraph, options.inferenceSourceRoot ?? options.erasedRoot);
  const report: RestoreReport = {
    annotations: 0,
    inferred: 0,
    unannotated: 0,
    syntaxFallback: 0,
    files: 0,
    invalidSpans: [],
  };

  for (const [relative, annotations] of Object.entries(options.groundTruth)) {
    let file: string;
    try {
      file = resolveInside(output, relative);
    } catch {
      report.invalidSpans.push({ file: relative, reason: "path escapes output directory" });
      continue;
    }
    if (!fs.existsSync(file)) {
      report.invalidSpans.push({ file: relative, reason: "missing file" });
      continue;
    }
    const content = readSource(file);
    const edits: TextEdit[] = [];
    for (const annotation of annotations) {
      report.annotations++;
      const { annotationStart: start, annotationEnd: end } = annotation;
      if (!Number.isInteger(start) || !Number.isInteger(end) || start < 0 || start >= end
        || end > content.length || content.slice(start, end).trim()) {
        report.invalidSpans.push({ file: relative, identifier: annotation.identifier, reason: "invalid or non-erased range" });
        continue;
      }
      const key = `${normalPath(relative)}\0${annotation.line}\0${annotation.col}`;
      const result = annotationType(annotation, candidates.get(key) ?? []);
      if (!result.type) {
        report.unannotated++;
        edits.push({ file, start, end, text: " " });
      } else {
        report[result.matched ? "inferred" : "syntaxFallback"]++;
        edits.push({ file, start, end, text: `: ${result.type}` });
      }
    }
    writeSource(file, applyEditsToText(content, edits, relative));
    report.files++;
  }
  writeSource(path.join(output, "migration-report.json"), `${JSON.stringify(report, null, 2)}\n`);
  return report;
}
