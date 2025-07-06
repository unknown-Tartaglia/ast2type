import * as fs from "fs";
import * as path from "path";
import { Project, SyntaxKind, Node } from "ts-morph";
import { Command } from "commander";

// 解析命令行参数
const program = new Command();
program
  .requiredOption("-i, --input <inputDir>", "Input source code directory")
  .option("-o, --output <outputDir>", "Output AST directory (default: ./output/ast)");

program.parse(process.argv);
const options = program.opts();

const inputDir = path.resolve(options.input);
const outputDir = options.output ? path.resolve(options.output) : path.resolve("./output/ast");

// 初始化 ts-morph 项目
const project = new Project({
  tsConfigFilePath: path.resolve("./tsconfig.json"),
  skipAddingFilesFromTsConfig: true,
  compilerOptions: {
    allowJs: true,
  },
});

// 黑名单节点集合，空时表示不忽略任何节点
const ignoredKinds = new Set<SyntaxKind>([
  // 示例，删掉注释和无用节点，实际用时可以清空
  SyntaxKind.EndOfFileToken,
  SyntaxKind.WhitespaceTrivia,
  SyntaxKind.NewLineTrivia,
  SyntaxKind.JSDocComment,
  SyntaxKind.JSDocTag,
  SyntaxKind.JSDocText,
]);

// 递归读取源码文件
function collectSourceFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files = files.concat(collectSourceFiles(fullPath));
    } else {
      if (
        (entry.name.endsWith(".ts") ||
          entry.name.endsWith(".tsx") ||
          entry.name.endsWith(".js") ||
          entry.name.endsWith(".ets")) &&
        !entry.name.endsWith(".d.ts")
      ) {
        files.push(fullPath);
      }
    }
  }
  return files;
}

// 递归序列化节点，黑名单节点和其子树完全剪掉
function serializeNode(node: Node): any | null {
  if (ignoredKinds.has(node.getKind())) {
    return null;
  }

  const children = node.getChildren()
    .map(serializeNode)
    .filter((c) => c !== null);

  const serialized: any = {
    kind: SyntaxKind[node.getKind()],
  };

  // 保留简短文本，方便调试
  const text = node.getText().trim();
  if (text.length > 0 && text.length <= 100) {
    serialized.text = text;
  }

  if (children.length > 0) {
    serialized.children = children;
  }

  // 记录位置信息
  const sourceFile = node.getSourceFile();
  const startPos = sourceFile.getLineAndColumnAtPos(node.getPos());
  const endPos = sourceFile.getLineAndColumnAtPos(node.getEnd());

  serialized.position = {
    start: { line: startPos.line, character: startPos.column },
    end: { line: endPos.line, character: endPos.column },
  };

  return serialized;
}

function main() {
  const sourceFiles = collectSourceFiles(inputDir);
  console.log(`Found ${sourceFiles.length} source files.`);

  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }

  for (const filePath of sourceFiles) {
    const sourceFile = project.addSourceFileAtPath(filePath);
    const astJson = serializeNode(sourceFile);

    const relativePath = path.relative(inputDir, filePath);
    const outputFileName = relativePath.replace(/[\/\\]/g, "_") + ".ast.json";
    const outputFilePath = path.join(outputDir, outputFileName);

    fs.writeFileSync(outputFilePath, JSON.stringify(astJson, null, 2), "utf8");
    console.log(`AST dumped: ${outputFilePath}`);
  }
}

main();
