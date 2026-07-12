import { Node, Project, SyntaxKind, SourceFile, TypeNode } from "ts-morph";
import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";

// CLI
const program = new Command();
program
  .requiredOption("-i, --input <inputDir>", "Input TypeScript source directory")
  .option("-o, --output <outputDir>", "Output directory for erased source and ground truth (default: ./erased)");
program.parse(process.argv);

const options = program.opts();
const inputDir = path.resolve(options.input);
const outputDir = options.output ? path.resolve(options.output) : path.resolve("./erased");

// Ground truth entry
interface AnnotationEntry {
  identifier: string;
  offset: number;
  annotationStart: number;
  annotationEnd: number;
  line: number;
  col: number;
  type: string;
  kind: "param" | "return" | "variable" | "property" | "index" | "index-value";
  isAsync?: boolean;
  inferable?: boolean;
  matchText?: boolean;
}

interface GroundTruth {
  [filePath: string]: AnnotationEntry[];
}

interface Replacement {
  start: number;
  end: number;
}

// ── helpers ──

const sourceExtension = /\.(ts|tsx|mts|cts|ets)$/;
const declarationExtension = /\.d\.(ts|mts|cts|ets)$/;
const ignoredDirectories = new Set([".git", "node_modules"]);

function findTsFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory() && !ignoredDirectories.has(entry.name)) {
      files = files.concat(findTsFiles(fullPath));
    }
    else if (entry.isFile() && sourceExtension.test(entry.name)) files.push(fullPath);
  }
  return files;
}

function lineColOf(sourceFile: SourceFile, pos: number): { line: number; col: number } {
  const r = sourceFile.getLineAndColumnAtPos(pos);
  return { line: r.line, col: r.column };
}

function annotationColon(typeNode: TypeNode): Node | undefined {
  const previous = typeNode.getPreviousSibling();
  return previous?.getKind() === SyntaxKind.ColonToken ? previous : undefined;
}

function declarationIdentity(node: any): { node: Node; inferable: boolean; matchText: boolean } {
  const nameNode: Node | undefined = typeof node.getNameNode === "function"
    ? node.getNameNode()
    : undefined;
  if (!nameNode) return { node, inferable: true, matchText: false };
  if (Node.isIdentifier(nameNode)) {
    return { node: nameNode, inferable: true, matchText: true };
  }
  // The current inference graph has no declaration slot for binding patterns
  // or quoted/computed property names. They are still erased, but are not
  // matched to an unrelated descendant node during restoration.
  return { node: nameNode, inferable: false, matchText: false };
}

function functionIdentity(node: any): { node: Node; inferable: boolean; matchText: boolean } {
  const identity = declarationIdentity(node);
  if (identity.node !== node || typeof node.getNameNode === "function") return identity;
  // Anonymous arrows/functions are represented by their function node in the
  // graph. Their text changes after erasure, so position is the stable key.
  return { node, inferable: true, matchText: false };
}

function isReturnTypedFunction(node: Node): boolean {
  return Node.isFunctionDeclaration(node)
    || Node.isMethodDeclaration(node)
    || Node.isMethodSignature(node)
    || Node.isArrowFunction(node)
    || Node.isFunctionExpression(node)
    || Node.isGetAccessorDeclaration(node)
    || Node.isCallSignatureDeclaration(node)
    || Node.isConstructSignatureDeclaration(node);
}

// Merge overlapping replacement ranges
function mergeReplacements(r: Replacement[]): Replacement[] {
  if (r.length === 0) return [];
  const sorted = r.slice().sort((a, b) => a.start - b.start);
  const merged: Replacement[] = [sorted[0]];
  for (let i = 1; i < sorted.length; i++) {
    const last = merged[merged.length - 1];
    const curr = sorted[i];
    if (curr.start <= last.end) {
      last.end = Math.max(last.end, curr.end);
    } else {
      merged.push(curr);
    }
  }
  return merged;
}

// ── main ──

function main() {
  const groundTruth: GroundTruth = {};
  fs.mkdirSync(outputDir, { recursive: true });

  const project = new Project({
    skipAddingFilesFromTsConfig: true,
    compilerOptions: { allowJs: true },
  });

  const tsFiles = findTsFiles(inputDir);
  let totalAnnotations = 0;
  let totalFilesWithTypes = 0;

  for (const absFilePath of tsFiles) {
    const relativePath = path.relative(inputDir, absFilePath);
    const sourceFile = project.addSourceFileAtPath(absFilePath);
    const originalText = sourceFile.getFullText();

    // Declaration files are compile-time dependencies, not inference targets.
    // Preserve them verbatim so imports remain resolvable without exposing
    // their annotations as evaluation candidates.
    if (declarationExtension.test(absFilePath)) {
      const outPath = path.join(outputDir, relativePath);
      fs.mkdirSync(path.dirname(outPath), { recursive: true });
      fs.writeFileSync(outPath, originalText, "utf8");
      continue;
    }

    const annotations: AnnotationEntry[] = [];

    const record = (
      typeNode: TypeNode | undefined,
      identity: { node: Node; inferable: boolean; matchText: boolean },
      kind: AnnotationEntry["kind"],
      extra: Pick<AnnotationEntry, "isAsync"> = {},
    ) => {
      if (!typeNode) return;
      const colon = annotationColon(typeNode);
      if (!colon) return;
      const pos = lineColOf(sourceFile, identity.node.getStart());
      annotations.push({
        identifier: identity.node.getText(),
        offset: identity.node.getStart(),
        annotationStart: colon.getStart(),
        annotationEnd: typeNode.getEnd(),
        line: pos.line,
        col: pos.col,
        type: typeNode.getText(),
        kind,
        inferable: identity.inferable,
        matchText: identity.matchText,
        ...extra,
      });
    };

    // Typed/return-typed AST APIs cover all TypeScript type node forms. This
    // avoids leaking forms omitted by a SyntaxKind whitelist (for example
    // `keyof T`, constructor types, and import types).
    sourceFile.forEachDescendant((node: Node) => {
      if (Node.isParameterDeclaration(node)) {
        const isIndexKey = Node.isIndexSignatureDeclaration(node.getParent());
        record(
          node.getTypeNode(),
          declarationIdentity(node),
          isIndexKey ? "index" : "param",
        );
        return;
      }
      if (Node.isVariableDeclaration(node)) {
        record(node.getTypeNode(), declarationIdentity(node), "variable");
        return;
      }
      if (Node.isPropertyDeclaration(node)) {
        record(node.getTypeNode(), declarationIdentity(node), "variable");
        return;
      }
      if (Node.isPropertySignature(node)) {
        record(node.getTypeNode(), declarationIdentity(node), "property");
        return;
      }
      if (Node.isIndexSignatureDeclaration(node)) {
        const keyNode = node.getKeyNameNode();
        record(
          node.getReturnTypeNode(),
          { node: keyNode, inferable: false, matchText: false },
          "index-value",
        );
        return;
      }
      if (isReturnTypedFunction(node)) {
        const returnNode = (node as any).getReturnTypeNode() as TypeNode | undefined;
        record(returnNode, functionIdentity(node), "return", {
          isAsync: typeof (node as any).isAsync === "function"
            ? (node as any).isAsync()
            : false,
        });
      }
    });

    // A declaration type can contain nested property/index annotations. Its
    // outer replacement already erases those characters, so recording both
    // would create overlapping restoration ranges.
    const effectiveAnnotations = annotations.filter((annotation, index) =>
      !annotations.some((outer, outerIndex) =>
        outerIndex !== index
        && outer.annotationStart <= annotation.annotationStart
        && outer.annotationEnd >= annotation.annotationEnd
        && (outer.annotationStart < annotation.annotationStart
          || outer.annotationEnd > annotation.annotationEnd)
      )
    );
    const effectiveReplacements = effectiveAnnotations.map(annotation => ({
      start: annotation.annotationStart,
      end: annotation.annotationEnd,
    }));

    // Apply erasure (sort descending to preserve offsets). Write every
    // supported TS-family source so the inference tree keeps its file layout.
    let erasedText = originalText;
    if (effectiveReplacements.length > 0) {
      const merged = mergeReplacements(effectiveReplacements);
      merged.sort((a, b) => b.start - a.start);
      for (const { start, end } of merged) {
        const segment = erasedText.substring(start, end);
        erasedText = erasedText.substring(0, start)
          + segment.replace(/\S/g, " ")
          + erasedText.substring(end);
      }
    }
    const outPath = path.join(outputDir, relativePath);
    fs.mkdirSync(path.dirname(outPath), { recursive: true });
    fs.writeFileSync(outPath, erasedText, "utf8");

    if (effectiveAnnotations.length > 0) {
      groundTruth[relativePath] = effectiveAnnotations;
      totalAnnotations += effectiveAnnotations.length;
      totalFilesWithTypes++;
    }
  }

  // Write ground truth JSON
  const gtPath = path.join(outputDir, "_groundtruth.json");
  fs.writeFileSync(gtPath, JSON.stringify(groundTruth, null, 2), "utf8");

  console.log(`Done. Processed ${tsFiles.length} files.`);
  console.log(`  Extracted ${totalAnnotations} type annotations from ${totalFilesWithTypes} files.`);
  console.log(`  Erased source → ${outputDir}`);
  console.log(`  Ground truth  → ${gtPath}`);
}

main();
