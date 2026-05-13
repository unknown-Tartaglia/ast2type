import { Project, SyntaxKind, SourceFile } from "ts-morph";
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
  line: number;
  col: number;
  type: string;
  kind: "param" | "return" | "variable";
}

interface GroundTruth {
  [filePath: string]: AnnotationEntry[];
}

interface Replacement {
  start: number;
  end: number;
}

// ── Type expression nodes: keyword types + compound types ──
const typeExpressionKinds = new Set([
  // keyword types
  SyntaxKind.NumberKeyword, SyntaxKind.StringKeyword, SyntaxKind.BooleanKeyword,
  SyntaxKind.VoidKeyword, SyntaxKind.AnyKeyword, SyntaxKind.UndefinedKeyword,
  SyntaxKind.UnknownKeyword, SyntaxKind.NeverKeyword, SyntaxKind.ObjectKeyword,
  SyntaxKind.SymbolKeyword, SyntaxKind.BigIntKeyword,
  // compound types
  SyntaxKind.TypeReference, SyntaxKind.ArrayType,
  SyntaxKind.UnionType, SyntaxKind.IntersectionType,
  SyntaxKind.FunctionType, SyntaxKind.TupleType,
  SyntaxKind.TypeLiteral, SyntaxKind.TypeQuery,
  SyntaxKind.TypePredicate, SyntaxKind.ParenthesizedType,
  SyntaxKind.LiteralType, SyntaxKind.IndexedAccessType,
  SyntaxKind.ConditionalType, SyntaxKind.MappedType,
  SyntaxKind.TemplateLiteralType,
]);

// ── Node kinds that may carry a return type annotation ──
const funcReturnKinds = new Set([
  SyntaxKind.FunctionDeclaration,
  SyntaxKind.MethodDeclaration,
  SyntaxKind.MethodSignature,
  SyntaxKind.ArrowFunction,
  SyntaxKind.FunctionExpression,
]);

// ── helpers ──

function findTsFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) files = files.concat(findTsFiles(fullPath));
    else if (/\.(ts|ets|tsx|mts)$/.test(entry.name)) files.push(fullPath);
  }
  return files;
}

function lineColOf(sourceFile: SourceFile, pos: number): { line: number; col: number } {
  const r = sourceFile.getLineAndColumnAtPos(pos);
  return { line: r.line, col: r.column };
}

function isTypeExpr(n: any): boolean {
  return typeExpressionKinds.has(n.getKind());
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

    const annotations: AnnotationEntry[] = [];
    const replacements: Replacement[] = [];

    // Walk every descendant to find ColonToken → TypeExpr sequences
    sourceFile.forEachDescendant((node: any) => {
      const nodeKind = node.getKind();
      const children = node.getChildren();        // includes tokens

      for (let i = 0; i < children.length - 1; i++) {
        // ── step 1: find ColonToken → TypeExpr ──
        if (children[i].getKind() !== SyntaxKind.ColonToken) continue;
        const typeNode = children[i + 1];
        if (!isTypeExpr(typeNode)) continue;

        const colon = children[i];
        const prev = i > 0 ? children[i - 1].getText() == '?' ? children[i - 2] : children[i - 1]  : null;

        // ── step 2: Identifier → ColonToken → TypeExpr  (param / variable) ──
        if (prev && prev.getKind() === SyntaxKind.Identifier) {
          let annKind: "param" | "variable" | undefined;
          if (nodeKind === SyntaxKind.Parameter) annKind = "param";
          else if (nodeKind === SyntaxKind.VariableDeclaration) annKind = "variable";
          else if (nodeKind === SyntaxKind.PropertyDeclaration || nodeKind === SyntaxKind.PropertySignature) annKind = "variable";
          if (!annKind) continue;

          const pos = lineColOf(sourceFile, prev.getStart());
          annotations.push({
            identifier: prev.getText(),
            offset: prev.getStart(),
            line: pos.line, col: pos.col,
            type: typeNode.getText(),
            kind: annKind,
          });
          replacements.push({ start: colon.getStart(), end: typeNode.getEnd() });
          continue;   // one annotation per colon, skip to next node
        }

        // ── step 3: arbitrary → ColonToken → TypeExpr  (return type) ──
        if (funcReturnKinds.has(nodeKind)) {
          // for named functions/methods, record the name node; for anonymous, the node itself
          let idNode: any = node;
          if (nodeKind !== SyntaxKind.ArrowFunction && nodeKind !== SyntaxKind.FunctionExpression) {
            idNode = children.find((c: any) => c.getKind() === SyntaxKind.Identifier) ?? node;
          }
          const pos = lineColOf(sourceFile, idNode.getStart());
          annotations.push({
            identifier: idNode.getText(),
            offset: idNode.getStart(),
            line: pos.line, col: pos.col,
            type: typeNode.getText(),
            kind: "return",
          });
          replacements.push({ start: colon.getStart(), end: typeNode.getEnd() });
          continue;
        }
      }
    });

    // Apply erasure (sort descending to preserve offsets)
    if (replacements.length > 0) {
      let erasedText = sourceFile.getFullText();
      const merged = mergeReplacements(replacements);
      merged.sort((a, b) => b.start - a.start);
      for (const { start, end } of merged) {
        erasedText = erasedText.substring(0, start)
          + " ".repeat(end - start)
          + erasedText.substring(end);
      }
      const outPath = path.join(outputDir, relativePath);
      fs.mkdirSync(path.dirname(outPath), { recursive: true });
      fs.writeFileSync(outPath, erasedText, "utf8");
    }

    if (annotations.length > 0) {
      groundTruth[relativePath] = annotations;
      totalAnnotations += annotations.length;
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
