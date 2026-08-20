import * as fs from "fs";
import * as path from "path";
import ts from "typescript";
import type { TextEdit, TypeGraph } from "./contracts";
import { applyEditsToText, readSource, resolveInside, writeSource } from "./files";
import { canonicalFunctionTargets, validType } from "./typegraph";
import type { FunctionTarget, TargetStats } from "./typegraph";

const SOURCE_EXTENSIONS = new Set([".js", ".mjs"]);
const IGNORED_DIRECTORIES = new Set(["node_modules", ".git"]);
type FunctionNode = ts.FunctionDeclaration | ts.FunctionExpression | ts.ArrowFunction
  | ts.MethodDeclaration | ts.ConstructorDeclaration | ts.GetAccessorDeclaration
  | ts.SetAccessorDeclaration;

export interface WeaveReport extends TargetStats {
  locatedTargets: number;
  wovenTargets: number;
  edits: number;
  skippedTargets: number;
  sourceFiles: number;
  modifiedFiles: number;
  modifiedPaths: string[];
  compatibilityNormalizedFiles: number;
  nodeGlobalDeclarationFiles: number;
  skipped: Array<{ id: number; file?: string; reason: string }>;
}

export interface WovenJavaScript {
  files: Map<string, string>;
  report: WeaveReport;
}

function sourceFiles(root: string): string[] {
  const files: string[] = [];
  const visit = (directory: string): void => {
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })
      .sort((left, right) => left.name.localeCompare(right.name))) {
      const target = path.join(directory, entry.name);
      if (entry.isDirectory()) {
        if (!IGNORED_DIRECTORIES.has(entry.name)) visit(target);
      } else if (entry.isFile() && SOURCE_EXTENSIONS.has(path.extname(entry.name).toLowerCase())) {
        files.push(path.resolve(target));
      }
    }
  };
  visit(root);
  return files;
}

function isFunctionNode(node: ts.Node): node is FunctionNode {
  return ts.isFunctionDeclaration(node) || ts.isFunctionExpression(node)
    || ts.isArrowFunction(node) || ts.isMethodDeclaration(node)
    || ts.isConstructorDeclaration(node) || ts.isGetAccessorDeclaration(node)
    || ts.isSetAccessorDeclaration(node);
}

function functionName(node: FunctionNode, source: ts.SourceFile): string | undefined {
  if (ts.isConstructorDeclaration(node)) return "constructor";
  if (node.name && (ts.isIdentifier(node.name) || ts.isStringLiteral(node.name) || ts.isNumericLiteral(node.name))) {
    return node.name.text;
  }
  if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) {
    const parent = node.parent;
    if (ts.isVariableDeclaration(parent) && ts.isIdentifier(parent.name)) return parent.name.text;
    if (ts.isPropertyAssignment(parent)) return parent.name.getText(source);
    if (ts.isBinaryExpression(parent) && parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
      return parent.left.getText(source);
    }
  }
  return undefined;
}

function functionIndex(source: ts.SourceFile): Map<number, FunctionNode[]> {
  const byStart = new Map<number, FunctionNode[]>();
  const visit = (node: ts.Node): void => {
    if (isFunctionNode(node) && node.body) {
      const start = node.getStart(source);
      const group = byStart.get(start) ?? [];
      group.push(node);
      byStart.set(start, group);
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  return byStart;
}

function bareArrowParameter(node: FunctionNode, parameter: ts.ParameterDeclaration, source: ts.SourceFile): boolean {
  return ts.isArrowFunction(node) && node.parameters.length === 1
    && node.parameters[0] === parameter && ts.isIdentifier(parameter.name)
    && !node.getChildren(source).some(child => child.kind === ts.SyntaxKind.OpenParenToken);
}

function restType(value: string): string {
  return value.endsWith("[]") || /^(?:Readonly)?Array\s*</.test(value) || value.startsWith("[")
    ? value
    : "any[]";
}

function identifierName(node: ts.Node | undefined): string | undefined {
  return node && (ts.isIdentifier(node) || ts.isPrivateIdentifier(node)
    || ts.isStringLiteral(node) || ts.isNumericLiteral(node))
    ? node.text
    : undefined;
}

function addClassFields(content: string, file: string): string {
  const source = ts.createSourceFile(file, content, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
  const edits: Array<Omit<TextEdit, "file">> = [];
  const visit = (node: ts.Node): void => {
    if (ts.isClassDeclaration(node) || ts.isClassExpression(node)) {
      const assigned = new Set<string>();
      const declared = new Set<string>();
      for (const member of node.members) {
        if (ts.isPropertyDeclaration(member)) {
          const name = identifierName(member.name);
          if (name) declared.add(name);
        }
      }
      const findAssignments = (child: ts.Node): void => {
        if (ts.isBinaryExpression(child)
          && child.operatorToken.kind === ts.SyntaxKind.EqualsToken
          && ts.isPropertyAccessExpression(child.left)
          && child.left.expression.kind === ts.SyntaxKind.ThisKeyword) {
          assigned.add(child.left.name.text);
        }
        ts.forEachChild(child, findAssignments);
      };
      for (const member of node.members) findAssignments(member);
      const missing = [...assigned].filter(name => !declared.has(name)).sort();
      if (missing.length) {
        const brace = node.getChildren(source).find(child => child.kind === ts.SyntaxKind.OpenBraceToken);
        if (brace) {
          const firstMember = node.members[0];
          const lineStart = firstMember
            ? content.lastIndexOf("\n", firstMember.getStart(source) - 1) + 1
            : -1;
          const indent = firstMember && lineStart >= 0
            ? content.slice(lineStart, firstMember.getStart(source)).match(/^\s*/)?.[0] || "  "
            : "  ";
          edits.push({
            start: brace.getEnd(),
            end: brace.getEnd(),
            text: missing.map(name => `\n${indent}${name}: any;`).join(""),
          });
        }
      }
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  return applyEditsToText(content, edits, file);
}

function normalizeDefaultExport(content: string, file: string): string {
  const source = ts.createSourceFile(file, content, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
  const edits: Array<Omit<TextEdit, "file">> = [];
  for (const statement of source.statements) {
    if (!ts.isExportAssignment(statement) || statement.isExportEquals
      || !ts.isBinaryExpression(statement.expression)
      || statement.expression.operatorToken.kind !== ts.SyntaxKind.EqualsToken) continue;
    const expression = statement.expression;
    if (!ts.isElementAccessExpression(expression.left)
      || !ts.isIdentifier(expression.left.expression)
      || !ts.isStringLiteral(expression.left.argumentExpression)
      || expression.left.argumentExpression.text !== "default") continue;
    const root = expression.left.expression.text;
    if (!ts.isBinaryExpression(expression.right)
      || expression.right.operatorToken.kind !== ts.SyntaxKind.EqualsToken
      || !ts.isPropertyAccessExpression(expression.right.left)
      || !ts.isIdentifier(expression.right.left.expression)
      || expression.right.left.expression.text !== root
      || !ts.isIdentifier(expression.right.right)
      || expression.right.right.text !== root) continue;
    edits.push({
      start: statement.getStart(source),
      end: statement.getEnd(),
      text: `${expression.getText(source)};\nexport default ${root};`,
    });
  }
  return applyEditsToText(content, edits, file);
}

const NODE_GLOBALS: Record<string, string> = {
  exports: "var exports: any",
  module: "var module: { exports: any; [key: string]: any }",
  process: "var process: any",
  Buffer: "var Buffer: any",
  __dirname: "var __dirname: string",
  __filename: "var __filename: string",
  global: "var global: any",
  define: "function define(...args: any[]): any",
  require: "function require(name: string): any",
};

function isDeclarationName(node: ts.Identifier): boolean {
  const parent = node.parent;
  return ((ts.isVariableDeclaration(parent) || ts.isParameter(parent)
      || ts.isFunctionDeclaration(parent) || ts.isClassDeclaration(parent)
      || ts.isImportClause(parent) || ts.isImportSpecifier(parent)
      || ts.isNamespaceImport(parent)) && parent.name === node)
    || (ts.isPropertyAccessExpression(parent) && parent.name === node)
    || (ts.isPropertyAssignment(parent) && parent.name === node && parent.initializer !== node)
    || (ts.isPropertyDeclaration(parent) && parent.name === node)
    || (ts.isMethodDeclaration(parent) && parent.name === node);
}

function injectNodeGlobals(content: string, file: string): string {
  const source = ts.createSourceFile(file, content, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
  const referenced = new Set<string>();
  const declared = new Set<string>();
  const visit = (node: ts.Node): void => {
    if (ts.isIdentifier(node) && Object.prototype.hasOwnProperty.call(NODE_GLOBALS, node.text)) {
      (isDeclarationName(node) ? declared : referenced).add(node.text);
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  const needed = Object.keys(NODE_GLOBALS).filter(name => referenced.has(name) && !declared.has(name));
  if (!needed.length) return content;

  let position = 0;
  if (content.startsWith("#!")) {
    const newline = content.indexOf("\n");
    position = newline < 0 ? content.length : newline + 1;
  }
  const first = source.statements[0];
  if (first && ts.isExpressionStatement(first) && ts.isStringLiteral(first.expression)
    && first.expression.text === "use strict") {
    position = first.getEnd();
    while (content[position] === "\r" || content[position] === "\n") position++;
  }
  const block = `${needed.map(name => `declare ${NODE_GLOBALS[name]};`).join("\n")}\n`;
  return content.slice(0, position) + block + content.slice(position);
}

function normalizeCompatibility(content: string, file: string): { content: string; normalized: boolean; globals: boolean } {
  const classFields = addClassFields(content, file);
  const defaultExport = normalizeDefaultExport(classFields, file);
  const withPredicateTypes = injectPredicateFallbackTypes(defaultExport);
  const withGlobals = injectNodeGlobals(withPredicateTypes, file);
  return {
    content: withGlobals,
    normalized: withPredicateTypes !== content,
    globals: withGlobals !== withPredicateTypes,
  };
}

/**
 * A type predicate can name a public type that was erased from a JavaScript
 * source file.  Keep the predicate in the emitted declaration, but provide a
 * local fallback alias so the migrated implementation still type-checks.
 * Existing declarations/imports always win; qualified names are skipped.
 */
function injectPredicateFallbackTypes(content: string): string {
  const names = new Set<string>();
  const declared = new Set<string>();
  const declarationPattern = /\b(?:type|interface|class|enum|function|const|let|var)\s+([A-Za-z_$][\w$]*)/g;
  for (const match of content.matchAll(declarationPattern)) declared.add(match[1]);
  const importPattern = /\bimport\s+(?:type\s+)?(?:\{([^}]+)\}|([A-Za-z_$][\w$]*))/g;
  for (const match of content.matchAll(importPattern)) {
    for (const item of (match[1] ?? match[2] ?? "").split(",")) {
      const name = item.trim().split(/\s+as\s+/).pop()?.trim();
      if (name) declared.add(name);
    }
  }
  const predicatePattern = /\b[A-Za-z_$][\w$]*\s+is\s+([A-Za-z_$][\w$]*)\b/g;
  for (const match of content.matchAll(predicatePattern)) {
    if (!declared.has(match[1])) names.add(match[1]);
  }
  if (!names.size) return content;
  const aliases = [...names].map(name => `type ${name} = any;`).join("\n") + "\n";
  let position = 0;
  if (content.startsWith("#!")) {
    const newline = content.indexOf("\n");
    position = newline < 0 ? content.length : newline + 1;
  }
  const directive = content.slice(position).match(/^(?:\s*)(["']use strict["'];\s*)/);
  if (directive) position += directive[0].length;
  return content.slice(0, position) + aliases + content.slice(position);
}

function editsForFunction(
  target: FunctionTarget,
  node: FunctionNode,
  source: ts.SourceFile,
  relativeFile: string,
): TextEdit[] {
  const edits: TextEdit[] = [];
  node.parameters.forEach((parameter, index) => {
    if (parameter.type) return;
    let type = target.parameterTypes[index]?.trim() || "any";
    if (!validType(type)) type = parameter.dotDotDotToken ? "any[]" : "any";
    if (parameter.dotDotDotToken) type = restType(type);
    if (bareArrowParameter(node, parameter, source)) {
      edits.push({
        file: relativeFile,
        start: parameter.name.getStart(source),
        end: parameter.name.getEnd(),
        text: `(${parameter.name.getText(source)}: ${type})`,
      });
    } else {
      const position = parameter.questionToken?.getEnd() ?? parameter.name.getEnd();
      edits.push({ file: relativeFile, start: position, end: position, text: `: ${type}` });
    }
  });

  if (!ts.isConstructorDeclaration(node) && !ts.isSetAccessorDeclaration(node) && !node.type) {
    let returnType = target.returnType.trim();
    const predicate = returnType.match(/^(asserts\s+)?([A-Za-z_$][\w$]*)\s+is\s+(.+)$/);
    const firstParameter = node.parameters[0]?.name;
    if (predicate && firstParameter && ts.isIdentifier(firstParameter)) {
      const assertion = predicate[1] ?? "";
      returnType = `${assertion}${firstParameter.text} is ${predicate[3]}`;
    }
    if (!validType(returnType)) returnType = "any";
    const async = node.modifiers?.some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword);
    if (async && !/^Promise\s*</.test(returnType)) {
      returnType = returnType === "Promise" ? "Promise<any>" : `Promise<${returnType}>`;
    }
    const position = ts.isArrowFunction(node)
      ? node.equalsGreaterThanToken.getStart(source)
      : node.body!.getStart(source);
    edits.push({ file: relativeFile, start: position, end: position, text: `: ${returnType} ` });
  }
  return edits;
}

export function weaveJavaScript(sourceRoot: string, typegraph: TypeGraph): WovenJavaScript {
  const root = path.resolve(sourceRoot);
  const { targets, stats } = canonicalFunctionTargets(typegraph);
  const targetsByFile = new Map<string, FunctionTarget[]>();
  const skipped: WeaveReport["skipped"] = [];
  for (const target of targets) {
    let file: string;
    try {
      file = resolveInside(root, path.isAbsolute(target.file) ? path.relative(root, target.file) : target.file);
    } catch {
      skipped.push({ id: target.id, file: target.file, reason: "file-outside-source-root" });
      continue;
    }
    if (!fs.existsSync(file)) {
      skipped.push({ id: target.id, file: target.file, reason: "missing-file" });
      continue;
    }
    const group = targetsByFile.get(file) ?? [];
    group.push(target);
    targetsByFile.set(file, group);
  }

  const files = new Map<string, string>();
  const modifiedPaths: string[] = [];
  let locatedTargets = 0;
  let wovenTargets = 0;
  let editCount = 0;
  let compatibilityNormalizedFiles = 0;
  let nodeGlobalDeclarationFiles = 0;
  for (const file of sourceFiles(root)) {
    const relative = path.relative(root, file);
    const content = readSource(file);
    const source = ts.createSourceFile(
      file,
      content,
      ts.ScriptTarget.Latest,
      true,
      path.extname(file).toLowerCase() === ".jsx" ? ts.ScriptKind.JSX : ts.ScriptKind.JS,
    );
    const index = functionIndex(source);
    const edits: TextEdit[] = [];
    for (const target of targetsByFile.get(file) ?? []) {
      let position: number;
      try {
        position = source.getPositionOfLineAndCharacter(target.line - 1, target.column - 1);
      } catch {
        skipped.push({ id: target.id, file: relative, reason: "position-out-of-range" });
        continue;
      }
      const matches = index.get(position) ?? [];
      if (matches.length !== 1) {
        skipped.push({ id: target.id, file: relative, reason: matches.length ? "ambiguous-position" : "position-mismatch" });
        continue;
      }
      locatedTargets++;
      const node = matches[0];
      const targetEdits = editsForFunction(target, node, source, relative);
      if (targetEdits.length) wovenTargets++;
      edits.push(...targetEdits);
      // Position is authoritative; names are retained only for diagnostics.
      void functionName(node, source);
    }
    const woven = applyEditsToText(content, edits, relative);
    const compatibility = normalizeCompatibility(woven, file);
    const updated = compatibility.content;
    files.set(relative, updated);
    editCount += edits.length;
    if (compatibility.normalized) compatibilityNormalizedFiles++;
    if (compatibility.globals) nodeGlobalDeclarationFiles++;
    if (updated !== content) modifiedPaths.push(relative.split(path.sep).join("/"));
  }
  return {
    files,
    report: {
      ...stats,
      locatedTargets,
      wovenTargets,
      edits: editCount,
      skippedTargets: skipped.length,
      sourceFiles: files.size,
      modifiedFiles: modifiedPaths.length,
      modifiedPaths,
      compatibilityNormalizedFiles,
      nodeGlobalDeclarationFiles,
      skipped,
    },
  };
}

export function writeJavaScriptMigration(outputRoot: string, woven: WovenJavaScript): void {
  const root = path.resolve(outputRoot);
  if (fs.existsSync(root)) throw new Error(`output directory already exists: ${root}`);
  fs.mkdirSync(root, { recursive: true });
  for (const [relative, content] of woven.files) {
    const extension = path.extname(relative).toLowerCase();
    const output = SOURCE_EXTENSIONS.has(extension)
      ? `${relative.slice(0, -extension.length)}.ts`
      : relative;
    writeSource(resolveInside(root, output), content);
  }
  writeSource(path.join(root, "migration-report.json"), `${JSON.stringify(woven.report, null, 2)}\n`);
}
