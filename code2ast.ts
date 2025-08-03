import * as fs from "fs";
import * as path from "path";
import { Project, SyntaxKind, Node, SourceFile } from "ts-morph";
import { Command } from "commander";
import JSON5 from "json5";

const program = new Command();
program
  .option("-i, --input <inputDir>", "Input source code directory or ArkTS project root")
  .option("-o, --output <outputDir>", "Output AST directory (default: ./output/ast)");

program.parse(process.argv);
const options = program.opts();

const fallbackInputDir = path.resolve("./");
const userInputDir = options.input ? path.resolve(options.input) : fallbackInputDir;
const outputDir = options.output ? path.resolve(options.output) : path.resolve("./output/ast");

const project = new Project({
  tsConfigFilePath: path.resolve("./tsconfig.json"),
  skipAddingFilesFromTsConfig: true,
  compilerOptions: { allowJs: true },
});

const ignoredKinds = new Set<SyntaxKind>([
  SyntaxKind.EndOfFileToken,
  SyntaxKind.WhitespaceTrivia,
  SyntaxKind.NewLineTrivia,
  SyntaxKind.JSDocComment,
  SyntaxKind.JSDocTag,
  SyntaxKind.JSDocText,
]);

const SDKRoots = [
  "D:\\DevEco Studio\\sdk\\default\\openharmony\\ets\\api\\",
  "D:\\DevEco Studio\\sdk\\default\\openharmony\\ets\\kits\\",
];
let srcFiles : string[] = [];
const globalImportMap = new Map<string, string>();

const visitedFiles = new Set<string>();

function findNodesByKind(root: Node, kind: SyntaxKind): Node[] {
  const found: Node[] = [];
  function walk(n: Node) {
    if (n.getKind() === kind) found.push(n);
    for (const child of n.getChildren()) walk(child);
  }
  walk(root);
  return found;
}

function findFileInRoots(rootDirs: string[], targetFileName: string): string | null {
  for (const dir of rootDirs) {
    const found = findFileRecursive(dir, targetFileName);
    if (found) return found;
  }
  console.error(`Failed to find ${targetFileName} at ${rootDirs}`);
  return null;
}

function findFileRecursive(rootDir: string, targetFileName: string): string | null {
  if (!fs.existsSync(rootDir)) return null;

  const suffixes = [".ts", ".js", ".ets", ".tsx", ".d.ts", ".d.ets"];

  // 检查 rootDir 目录本身是否包含目标文件（带后缀）
  for (const suffix of suffixes) {
    const directPath = path.join(rootDir, targetFileName + suffix);
    if (fs.existsSync(directPath)) {
      console.log(`Find import file ${directPath}`);
      return directPath;
    }
  }

  // 如果 rootDir 本身名称等于 targetFileName（作为模块处理）
  if (fs.existsSync(path.join(rootDir, targetFileName))) {
    console.log(`Find import file module ${path.join(rootDir, targetFileName)}`);
    return path.join(rootDir, targetFileName);
  }

  const entries = fs.readdirSync(rootDir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = path.join(rootDir, entry.name);

    if (entry.isDirectory()) {
      const result = findFileRecursive(fullPath, targetFileName);
      if (result) return result;
    }
  }

  return null;
}


function serializeNode(node: Node, isSDK: boolean, kitImports: string[]): any | null {
  if (ignoredKinds.has(node.getKind())) return null;

  const children = node.getChildren()
    .map(c => serializeNode(c, isSDK, kitImports))
    .filter((c) => c !== null);

  const serialized: any = {
    kind: SyntaxKind[node.getKind()],
  };

  if (node.getKind() === SyntaxKind.ImportDeclaration) {
    const str = node.getChildren().find(c => c.getKind() === SyntaxKind.StringLiteral);
    const imptsNodes = findNodesByKind(node, SyntaxKind.Identifier);
    const impts = imptsNodes?.map(n => n.getText());

    if (str && (kitImports.length === 0 || kitImports.filter(impt => impts.includes(impt)).length > 0)) {
      let importPath = str.getText().replace(/['"]/g, "");
      const currentFile = node.getSourceFile().getFilePath();
      let fullPath: string | null = null;
      let newKitImports : string[] = [];
      let isNextSDK = false;
      if (importPath.startsWith(".")) {
        const baseDir = path.dirname(currentFile);
        fullPath = findFileInRoots([path.resolve(baseDir)], importPath);
        isNextSDK = isSDK;
      } else if (importPath.startsWith("@")) {
        fullPath = findFileInRoots(SDKRoots, importPath);
        isNextSDK = true;
        if(importPath.startsWith("@kit"))
          newKitImports = impts;
      } else {
        // mobileimsdk/Index视为mobileimsdk
        importPath = importPath.split("/")[0];
        fullPath = findFileInRoots([userInputDir], "oh_modules/" + importPath);
        if (fullPath) fullPath = fullPath + "\\Index.d.ets";
      }
      console.log(`processing import ${node.getText()}: find path ${fullPath}`)
      dumpFile(fullPath, isNextSDK, newKitImports, importPath);
    }
  }

  const text = node.getText().trim();
  if (text.length > 0 && text.length <= 100) {
    serialized.text = text;
  }
  if (children.length > 0) serialized.children = children;

  const sourceFile = node.getSourceFile();
  const startPos = sourceFile.getLineAndColumnAtPos(node.getPos());
  const endPos = sourceFile.getLineAndColumnAtPos(node.getEnd());
  serialized.position = {
    start: { line: startPos.line, character: startPos.column },
    end: { line: endPos.line, character: endPos.column },
  };

  return serialized;
}

function dumpFile(filePath: string | null, isSDK = false, kitImports : string[] = [], importPath : string = "") {
  if (!filePath || !fs.existsSync(filePath)) return;
  const absPath = path.resolve(filePath);
  if (visitedFiles.has(absPath)) return;
  visitedFiles.add(absPath);
  const sourceFile = project.addSourceFileAtPath(absPath);
  const astJson = serializeNode(sourceFile, isSDK, kitImports);
  let relativePath : string;
  let outputFilePath : string;
  if (!isSDK) {
    relativePath = path.relative(userInputDir, absPath);
    const outputFileName = relativePath.replace(/[\/\\]/g, "^") + ".ast.json";
    outputFilePath = path.join(outputDir, outputFileName);
  }
  else {
    relativePath = path.relative("D:\\DevEco Studio\\sdk\\default\\openharmony\\ets\\", absPath);
    const outputFileName = relativePath.replace(/[\/\\]/g, "^") + ".ast.json";
    outputFilePath = path.join(outputDir + "/sdk", outputFileName);
  }
  fs.mkdirSync(path.dirname(outputFilePath), { recursive: true });
  fs.writeFileSync(outputFilePath, JSON.stringify(astJson, null, 2), "utf8");
  console.log(`AST dumped: ${outputFilePath}`);
  if (importPath !== "") globalImportMap.set(importPath, outputFilePath); 
}

function collectSourceFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files = files.concat(collectSourceFiles(fullPath));
    } else if (entry.name.match(/\.(ts|tsx|js|ets)$/)) {
      files.push(fullPath);
    }
  }
  return files;
}

function resolveArktsSourceRoots(rootDir: string): string[] {
  const profilePath = path.join(rootDir, "build-profile.json5");
  if (!fs.existsSync(profilePath)) return [];
  try {
    const profileText = fs.readFileSync(profilePath, "utf8");
    const profile = JSON5.parse(profileText);
    const modules = profile.modules ?? [];
    const srcRoots: string[] = [];
    for (const module of modules) {
      if (typeof module?.srcPath === "string") {
        const fullPath = path.resolve(rootDir, module.srcPath, "src", "main", "ets");
        if (fs.existsSync(fullPath)) srcRoots.push(fullPath);
      }
    }
    return srcRoots;
  } catch (err) {
    console.error("Failed to parse build-profile.json5:", err);
    return [];
  }
}

function main() {
  const sourceRoots = resolveArktsSourceRoots(userInputDir);
  const inputDirs = sourceRoots.length > 0 ? sourceRoots : [userInputDir];
  srcFiles = inputDirs.flatMap(collectSourceFiles);
  console.log(`Found ${srcFiles.length} source files.`);
  if (!fs.existsSync(outputDir)) fs.mkdirSync(outputDir, { recursive: true });
  for (const filePath of srcFiles) dumpFile(filePath);
  console.log(`${[...globalImportMap.values()]}`);
  fs.writeFileSync(path.resolve(outputDir, "../importMap.json"), JSON.stringify([...globalImportMap], null, 2), "utf8");
}

main();
