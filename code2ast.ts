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
const outputDir = options.output ? path.resolve(options.output + "/ast") : path.resolve(options.input.replace(/[\\\/]+$/, "") + "_output/ast");

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
  "E:\\type_extract\\node_modules\\",
  "E:\\type_extract\\tests\\node_modules\\",
];
let srcFiles : string[] = [];
const globalImportMap = new Map<string, string>();
const suffixes = ["", ".ts", ".js", ".mjs", ".ets", ".tsx", ".d.ts", ".d.ets", ".android.bundle"];
const visitedFiles = new Set<string>();

// 查找root下对应类型节点
function findNodesByKind(root: Node, kind: SyntaxKind): Node[] {
  const found: Node[] = [];
  function walk(n: Node) {
    if (n.getKind() === kind) found.push(n);
    for (const child of n.getChildren()) walk(child);
  }
  walk(root);
  return found;
}

// 在SDKroots下查找模块
function findFileInRoots(rootDirs: string[], targetFileName: string): string | null {
  for (const dir of rootDirs) {
    const found = findFile(dir, targetFileName, true);
    if (found) return found;
  }
  console.error(`Failed to find ${targetFileName} at ${rootDirs}`);
  return null;
}

// 在root下递归查找文件
function findFileRecursive(rootDir: string, targetFileName: string, allowDir: boolean): string | null {
  if (!fs.existsSync(rootDir)) return null;

  // 检查 rootDir 是否包含目标文件（带后缀）
  const ret = findFile(rootDir, targetFileName, allowDir);
  if (ret) return ret;

  const entries = fs.readdirSync(rootDir, { withFileTypes: true });
  for (const entry of entries) 
    if (entry.isDirectory()) {
      const result = findFileRecursive(path.join(rootDir, entry.name), targetFileName, allowDir);
      if (result) return result;
    }

  return null;
}

// 在root目录下查找文件
function findFile(root: string, targetFileName: string, allowDir: boolean): string | null {
  if (!fs.existsSync(root)) return null;

  for (const suffix of suffixes) {
    const directPath = path.join(root, targetFileName + suffix);
    if (fs.existsSync(directPath)) {
      return directPath;
    }
  }

  return allowDir ? fs.existsSync(path.join(root, targetFileName)) ? path.join(root, targetFileName) : null : null;
}


function serializeNode(node: Node, isSDK: boolean, kitImports: string[]): any | null {
  if (ignoredKinds.has(node.getKind())) return null;

  const children = node.getChildren()
    .map(c => serializeNode(c, isSDK, kitImports))
    .filter((c) => c !== null);

  const serialized: any = {
    kind: SyntaxKind[node.getKind()],
  };

  if (node.getKind() === SyntaxKind.ImportDeclaration || node.getKind() === SyntaxKind.ExportDeclaration) {
    const str = node.getChildren().find(c => c.getKind() === SyntaxKind.StringLiteral);
    const imptsNodes = findNodesByKind(node, SyntaxKind.Identifier).concat(findNodesByKind(node, SyntaxKind.AsteriskToken));
    const impts = imptsNodes?.map(n => n.getText());

    if (str && (!isSDK || kitImports.filter(impt => impts.includes(impt)).length > 0 || kitImports.includes("*") || impts.includes("*"))) {
      let importPath = str.getText().replace(/['"]/g, "");
      const currentFile = node.getSourceFile().getFilePath();
      let fullPath: string | null;
      let newKitImports : string[] = impts;
      let isNextSDK : boolean;
      let resolved: string | null = null;

      if (importPath.startsWith(".")) {
        const baseDir = path.parse(currentFile).dir;
        fullPath = path.resolve(baseDir, importPath);
        isNextSDK = isSDK;

        // 如果 fullPath 是目录，尝试解析 index.xxx
        if (fullPath && fs.existsSync(fullPath) && fs.statSync(fullPath).isDirectory()) {
          resolved = findFile(fullPath, "index", false);
          if (!resolved) console.warn(`Cannot resolve entry file in directory: ${fullPath}`);
        } else {
          resolved = findFile(path.parse(fullPath).dir, path.parse(fullPath).name, false);
          if (!resolved) console.warn(`cannot find import ${importPath} at path ${baseDir}, trying ${path.parse(fullPath).dir} + ${path.parse(fullPath).name}`);
        }
      } else {
        fullPath = findFileInRoots(SDKRoots, importPath);
        isNextSDK = true;

        // 如果 fullPath 是目录
        if (fullPath && fs.existsSync(fullPath) && fs.statSync(fullPath).isDirectory()) {
          const pkgPath = path.join(fullPath, "package.json");
          let fail = true;

          // 先解析pkg
          if (fs.existsSync(pkgPath)) {
            const pkg = JSON.parse(fs.readFileSync(pkgPath, "utf8"));
            const mainField = pkg.module || pkg.main;
            if (mainField && typeof mainField === "string") {
              const mainFull = path.resolve(fullPath, mainField);
              if (fs.existsSync(mainFull)) {
                // 如果不是目录，找到；否则找目录下index
                if (!fs.statSync(mainFull).isDirectory()) {
                  resolved = mainFull;
                  fail = false;
                  // console.log(`resolve entry via package.json : ${resolved}`);
                } else {
                  resolved = findFile(mainFull, "index", false);
                  if (resolved) {
                    fail = false;
                    // console.log(`resolve entry via package.json : ${resolved}`);
                  }
                }
              } else {
                resolved = findFile(path.parse(mainFull).dir, path.parse(mainFull).name, false);
                if (resolved) {
                  fail = false;
                  // console.log(`resolve entry via package.json : ${resolved}`);
                }
              }
            }
          }
          // 没成功就解析index
          if (fail) {
            resolved = findFile(fullPath, "index", false);
            if (resolved) {
              fail = false;
              // console.log(`resolve entry without package.json : ${resolved}`);
            }
          }
          // 都失败
          if (fail) console.warn(`Cannot resolve entry file in directory: ${fullPath}`);
        }
      }
      dumpFile(resolved, isNextSDK, newKitImports, importPath);
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
  if (!filePath) return;
  const absPath = path.resolve(filePath);
  if (visitedFiles.has(absPath)) return;
  if (!fs.existsSync(filePath)) {
    console.log(`no file ${filePath}`)
    return;
  }
  visitedFiles.add(absPath);
  console.log(`AST dumping: ${absPath}`);
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
    relativePath = absPath.replace(/:/, "");
    const outputFileName = relativePath.replace(/[\/\\]/g, "^") + ".ast.json";
    outputFilePath = path.join(outputDir + "/sdk", outputFileName);
  }
  fs.mkdirSync(path.parse(outputFilePath).dir, { recursive: true });
  fs.writeFileSync(outputFilePath, JSON.stringify(astJson, null, 2), "utf8");
  // writeJsonStream(outputFilePath, astJson);
  // console.log(`AST dumped: ${outputFilePath}`);
  if (importPath !== "") globalImportMap.set(importPath, outputFilePath); 
}

function collectSourceFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files = files.concat(collectSourceFiles(fullPath));
    } else if (entry.name.match(/\.(ts|tsx|js|mjs|ets|bundle)$/)) {
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
  // console.log(`${[...globalImportMap.values()]}`);
  fs.writeFileSync(path.resolve(outputDir, "../importMap.json"), JSON.stringify([...globalImportMap], null, 2), "utf8");
}

main();
