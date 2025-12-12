import * as fs from "fs";
import * as path from "path";
import { Project, SyntaxKind, Node, OutputFile } from "ts-morph";
import { Command } from "commander";
import JSON5 from "json5";
import { findNodeHandle } from "react-native";

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
let lineStarts: number[] = [];
const position = {
  "start": {
    "line": -1,
    "character": -1
  },
  "end": {
    "line": -1,
    "character": -1
  }
}

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

function buildLineMap(fileText: string): number[] {
  const lineStarts = [0];
  for (let i = 0; i < fileText.length; i++) {
    const ch = fileText.charCodeAt(i);
    if (ch === 10) { // \n
      lineStarts.push(i + 1);
    }
  }
  return lineStarts;
}

function getLineAndColumn(pos: number, lineStarts: number[]) {
  let low = 0;
  let high = lineStarts.length - 1;

  while (low <= high) {
    const mid = (low + high) >> 1;
    const lineStart = lineStarts[mid];

    if (lineStart === pos) {
      return { line: mid + 1, character: 1 };
    } else if (lineStart < pos) {
      low = mid + 1;
    } else {
      high = mid - 1;
    }
  }

  const line = high;
  return {
    line: line + 1,
    character: pos - lineStarts[line] + 1,
  };
}

// 构造import id from filePath的AST节点
function constructImportAST(id: string, filePath: string): any {
  return {
    "kind": "ImportDeclaration",
    "offset": 0,
    "children": [
      {
        "kind": "ImportKeyword",
        "offset": -1,
        "text": "import",
        position
      },
      {
        "kind": "ImportClause",
        "offset": -1,
        "children": [
          {
            "kind": "NamespaceImport",
            "offset": -1,
            "children": [
              {
                "kind": "AsteriskToken",
                "offset": -1,
                "text": "*",
                position
              },
              {
                "kind": "AsKeyword",
                "offset": -1,
                "text": "as",
                position
              },
              {
                "kind": "Identifier",
                "offset": -1,
                "text": id,
                position
              }
            ],
            position
          },
        ],
        "text": `* as ${id}`,
        position
      },
      {
        "kind": "FromKeyword",
        "offset": -1,
        "text": "from",
        position
      },
      {
        "kind": "StringLiteral",
        "offset": -1,
        "text": filePath,
        position
      },
      {
        "kind": "SemicolonToken",
        "offset": -1,
        "text": ";",
        position
      }]
  }
}

let _dependencyMap : string[] = [];
let __d_idx = 0;
function serializeNode(node: Node, isSDK: boolean, kitImports: string[]): any | null {
  if (ignoredKinds.has(node.getKind())) return null;

  const serialized: any = {
    kind: SyntaxKind[node.getKind()],
    offset: node.getStart()
  };

  // 先序遍历部分
  // 处理__d
  if (node.getKind() === SyntaxKind.CallExpression && node.getChildAtIndex(0).getKind() === SyntaxKind.Identifier && node.getChildAtIndex(0).getText() === "__d") {
    const stxlst = node.getChildAtIndex(2);
    const arglst = stxlst.getChildAtIndex(4).getChildAtIndex(1); // arguments list
    for (const arg of arglst.getChildren()) {
      if (arg.getKind() === SyntaxKind.StringLiteral) {
        _dependencyMap.push(arg.getText().replace(/['"]/g, ""));
      }
    }
  } else if (node.getKind() === SyntaxKind.CallExpression && node.getChildAtIndex(0).getKind() === SyntaxKind.Identifier && node.getChildAtIndex(0).getText() === "_$$_REQUIRE") {
    const idx = node.getChildAtIndex(2).getChildAtIndex(0).getChildAtIndex(2);
    if (idx && idx.getKind() === SyntaxKind.FirstLiteralToken) {
      const index = parseInt(idx.getText(), 10);
      const dep = _dependencyMap[index];
      if (dep) {
        if (node.getParent()?.getKind() === SyntaxKind.PropertyAccessExpression) {
          return {
            "kind": "Identifier",
            "offset": -1,
            "text": `__dep_${index}`,
            position
          }
        } else {
          return {
            "kind": "PropertyAccessExpression",
            "offset": -1,
            "children": [
              { 
                "kind": "Identifier",
                "offset": -1,
                "text": `__dep_${index}`,
                position
              },
              {
                "kind": "DotToken",
                "offset": -1,
                "text": ".",
                position
              },
              {
                "kind": "Identifier",
                "offset": -1,
                "text": "default",
                position
              }
            ],
            text: `__dep_${index}.default`,
            position
          }
        }
      }
    } else {
      console.warn(`Cannot parse dependency index in ${node.getText()}`);
    }
  }


  const children: any[] = [];
  for (const child of node.getChildren()) {
    const sc = serializeNode(child, isSDK, kitImports);
    if (sc !== null) children.push(sc);
  }


  // 后序处理部分
  // 处理__d
  if (node.getKind() === SyntaxKind.CallExpression && node.getChildAtIndex(0).getKind() === SyntaxKind.Identifier && node.getChildAtIndex(0).getText() === "__d") {
    const stxlst = node.getChildAtIndex(2);
    const module = stxlst.getChildAtIndex(2).getText().replace(/['"]/g, "");
    const outputFilePath = path.join(outputDir, module.replace(/[\/\\]/g, "^") + ".ast.json");
    const json = children[2].children[0].children[4].children[1];
    let imports = [];
    let cnt = 0;
    for (const dep in _dependencyMap) {
      imports.push(constructImportAST(`__dep_${cnt}`, _dependencyMap[cnt]));
      cnt += 1;
    }
    if (imports.length > 0 || json.children) json.children = imports.concat(json.children);
    _dependencyMap = [];
    fs.mkdirSync(path.parse(outputFilePath).dir, { recursive: true });
    writeJsonStream(outputFilePath, json); // module body
    globalImportMap.set(module, outputFilePath);
    console.log(`__d_idx = ${++__d_idx}`);
    return null;
  }
  // 处理module.exports = xxx和exports.default = xxx
  else if (node.getKind() === SyntaxKind.BinaryExpression && node.getChildAtIndex(0).getKind() === SyntaxKind.PropertyAccessExpression && (node.getChildAtIndex(0).getText() === "module.exports" || node.getChildAtIndex(0).getText() === "exports.default")) {
    const exportNode = children[2];
    return {
      "kind": "ExportAssignment",
      "offset": -1,
      "children": [
        {
          "kind": "ExportKeyword",
          "offset": -1,
          "text": "export",
          position
        },
        {
          "kind": "DefaultKeyword",
          "offset": -1,
          "text": "default",
          position
        },
        {
          ...exportNode
        }
      ],
      position
    }
  }
  // 处理exports.xxx = xxx
  else if (node.getKind() === SyntaxKind.BinaryExpression && node.getChildAtIndex(0).getKind() === SyntaxKind.PropertyAccessExpression && node.getChildAtIndex(0).getChildAtIndex(0).getText() === "exports") {
    const exportName = node.getChildAtIndex(0).getChildAtIndex(2).getText();
    const exportNode = children[2];
    return {
      "kind": "FirstStatement",
      "offset": -1,
      "children": [
        {
          "kind": "SyntaxList",
          "offset": -1,
          "children": [
            {
              "kind": "ExportKeyword",
              "offset": -1,
              "text": "export",
              position
            }
          ],
          "text": "export",
          position
        },
        {
          "kind": "VariableDeclarationList",
          "offset": -1,
          "children": [
            {
              "kind": "ConstKeyword",
              "offset": -1,
              "text": "const",
              position
            },
            {
              "kind": "SyntaxList",
              "offset": -1,
              "children": [
                {
                  "kind": "VariableDeclaration",
                  "offset": -1,
                  "children": [
                    {
                      "kind": "Identifier",
                      "offset": -1,
                      "text": exportName,
                      position
                    },
                    {
                      "kind": "FirstAssignment",
                      "offset": -1,
                      "text": "=",
                      position
                    },
                    {
                      ...exportNode
                    }
                  ]
                }
              ]
            }
          ]
        }
      ],
      position
    }
  }
  // 处理import/export
  else if (node.getKind() === SyntaxKind.ImportDeclaration || node.getKind() === SyntaxKind.ExportDeclaration) {
    const str = node.getChildren().find(c => c.getKind() === SyntaxKind.StringLiteral);
    const imptsNodes = findNodesByKind(node, SyntaxKind.Identifier).concat(findNodesByKind(node, SyntaxKind.AsteriskToken));
    const impts = imptsNodes?.map(n => n.getText());

    if (str && (!isSDK || kitImports.filter(impt => impts.includes(impt)).length > 0 || kitImports.includes("*") || impts.includes("*"))) {
      let importPath = str.getText().replace(/['"]/g, "");
      const currentFile = node.getSourceFile().getFilePath();
      let fullPath: string | null;
      let newKitImports: string[] = impts;
      let isNextSDK: boolean;
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
  
  if (children.length > 0) serialized.children = children;
  const text = node.getWidth() <= 100 ? node.getText() : "";
  if (text.length > 0 && text.length <= 100) {
    serialized.text = text;
  }
  const start = node.getStart();
  const end = node.getEnd();
  const startPos = getLineAndColumn(start, lineStarts);
  const endPos = getLineAndColumn(end, lineStarts);
  serialized.position = { start: startPos, end: endPos };

  return serialized;
}

export function writeJsonStream(file: string, obj: any) {
  const out = fs.createWriteStream(file, { flags: "w" });
  const indent = "  "; // 2 spaces
  let level = 0;

  function newline() {
    out.write("\n" + indent.repeat(level));
  }

  function writeValue(value: any) {
    if (value === null) {
      out.write("null");
    } else if (Array.isArray(value)) {
      out.write("[");
      level++;
      for (let i = 0; i < value.length; i++) {
        newline();
        writeValue(value[i]);
        if (i < value.length - 1) out.write(",");
      }
      level--;
      if (value.length > 0) newline();
      out.write("]");
    } else if (typeof value === "object") {
      out.write("{");
      const keys = Object.keys(value).filter(k => value[k] !== undefined);
      level++;
      keys.forEach((k, i) => {
        newline();
        out.write(JSON.stringify(k) + ": ");
        writeValue(value[k]);
        if (i < keys.length - 1) out.write(",");
      });
      level--;
      if (keys.length > 0) newline();
      out.write("}");
    } else {
      out.write(JSON.stringify(value));
    }
  }

  writeValue(obj);
  out.write("\n");
  out.end();
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
  lineStarts = buildLineMap(sourceFile.getFullText());
  let astJson = serializeNode(sourceFile, isSDK, kitImports);
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
  writeJsonStream(outputFilePath, astJson);
  if (importPath !== "") globalImportMap.set(importPath, outputFilePath);
}

function collectSourceFiles(dir: string): string[] {
  // 如果dir不是目录
  if (!fs.existsSync(dir) || !fs.statSync(dir).isDirectory()) return [dir];
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
  // 计时
  const start = Date.now();
  const sourceRoots = resolveArktsSourceRoots(userInputDir);
  const inputDirs = sourceRoots.length > 0 ? sourceRoots : [userInputDir];
  srcFiles = inputDirs.flatMap(collectSourceFiles);
  console.log(`Found ${srcFiles.length} source files.`);
  if (!fs.existsSync(outputDir)) fs.mkdirSync(outputDir, { recursive: true });
  for (const filePath of srcFiles) dumpFile(filePath);
  // console.log(`${[...globalImportMap.values()]}`);
  fs.writeFileSync(path.resolve(outputDir, "../importMap.json"), JSON.stringify([...globalImportMap], null, 2), "utf8");
  const end = Date.now();
  console.log(`AST generation completed in ${(end - start) / 1000} seconds.`);
}

main();
