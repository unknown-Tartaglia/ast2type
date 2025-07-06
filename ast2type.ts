import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";

// 命令行参数
const program = new Command();
program
  .requiredOption("-i, --input <inputDir>", "Input AST JSON directory")
  .option("-o, --output <outputDir>", "Output constraint directory (default: ./output/constraint)");
program.parse(process.argv);

const options = program.opts();
const inputDir = path.resolve(options.input);
const outputDir = options.output ? path.resolve(options.output) : path.resolve("./output/constraint");

interface AstNode {
  kind: string;
  text?: string;
  children?: AstNode[];
  varId?: number;
  childVarIds?: number[];
}

// 遍历目录下所有 .ast.json 文件
function getAstFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files = files.concat(getAstFiles(fullPath));
    } else if (entry.name.endsWith(".ast.json")) {
      files.push(fullPath);
    }
  }
  return files;
}

function processAstFile(inputFile: string, outputFile: string) {
  const astRoot: AstNode = JSON.parse(fs.readFileSync(inputFile, "utf8"));

  let typeVarCounter = 0;
  const vars: Record<number, { kind: string; text?: string; childVarIds: number[] }> = {};
  const universe = new Set<string>();
  const constraints: Array<[string, number, number | string, string]> = [];
  const typeEnv = new Map<string, number>();
  const functionEnv = new Map<string, string>();

  function getTypeVarId(node: AstNode): number {
    if (node.varId !== undefined) return node.varId;
    const id = typeVarCounter++;
    node.varId = id;
    return id;
  }

  const handlers: Record<string, (node: AstNode) => void> = {
    StringLiteral(node) {
      constraints.push(["hasType", node.varId!, "string", `${node.text!} ∈ string`]);
      universe.add("string");
    },
    NoSubstitutionTemplateLiteral(node) {
      constraints.push(["hasType", node.varId!, "string", `${node.text!} ∈ string`]);  
      universe.add("string");
    },
    NumericLiteral(node) {
      constraints.push(["hasType", node.varId!, "number", `${node.text!} ∈ number`]);
      universe.add("number");
    },
    TrueKeyword(node) {
      constraints.push(["hasType", node.varId!, "boolean", `${node.text!} ∈ boolean`]);
      universe.add("boolean");
    },
    FalseKeyword(node) {
      constraints.push(["hasType", node.varId!, "boolean", `${node.text!} ∈ boolean`]);
      universe.add("boolean");
    },
    NullKeyword(node) {
      constraints.push(["hasType", node.varId!, "null", `${node.text!} ∈ null`]);
      universe.add("null");
    },
    BigIntLiteral(node) {
      constraints.push(["hasType", node.varId!, "bigint", `${node.text!} ∈ bigint`]);
      universe.add("bigint");
    },
    // 二元操作
    BinaryExpression(node) {
      const hasAssignment = node.children?.some((c) => c.kind === "FirstAssignment");
      if (hasAssignment && node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        // 处理赋值操作
        if (left.varId !== undefined && right.varId !== undefined && operator.kind === "FirstAssignment") {
          constraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
          constraints.push(["sameType", node.varId!, right.varId, `${node.text!} = ${right.text!}`]);
        }
        // 处理其他二元操作
        else if (left.varId !== undefined && right.varId !== undefined) {
          constraints.push(["equalVal", left.varId!, right.varId, `${left.text!} == ${right.text!}`]);
          constraints.push(["sameType", node.varId!, right.varId, `${node.text!} = ${right.text!}`]);
        }
      }
    },
    // 变量声明
    VariableDeclaration(node) {
      // example: id [: type] = x
      if (node.children && node.children.length >= 3) {
        const left = node.children![0];
        if (node.children![1].text == ":") {
          // 处理带类型注解初始化
          if (left.varId !== undefined && node.children![2].varId !== undefined) {
            constraints.push(["sameType", left.varId, node.children![2].text!, `${left.text!} = ${node.children![2].text!}`]);
            typeEnv.set(left.text!, left.varId!);
            universe.add(node.children![2].text!);
          }
        }
        else {
          // 处理无类型注解初始化
          const operator = node.children![1];
          const right = node.children![2];
          if (left.varId !== undefined && right.varId !== undefined && operator.kind === "FirstAssignment") {
            constraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
            typeEnv.set(left.text!, left.varId!);
          }
        }
      }
    },
    // New运算符
    NewExpression(node) {
      if (node.children && node.children.length >= 5) {
        const classNode = node.children[1];
        if (classNode.varId !== undefined) {
          constraints.push(["sameType", node.varId!, classNode.text!, `new ${classNode.text!}`]);
          universe.add(classNode.text!);
        }
      }
    },
    // 处理标识符
    Identifier(node) {
      if (node.text) {
        const typeId = typeEnv.get(node.text);
        if (typeId !== undefined) {
          constraints.push(["sameType", node.varId!, typeId, `same identifier: ${node.text!}`]);
        }
      }
    },
    // 处理接口声明
    InterfaceDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children[1];
          universe.add(idNode.text!);
      }
    },
    // 处理接口Property
    PropertySignature(node) {
      if (node.children && node.children.length >= 3) {
        const idNode = node.children[0];
        if (node.children[1].kind === "ColonToken") {
          const typeNode = node.children[2];
          if (typeNode.varId !== undefined) {
            constraints.push(["sameType", idNode.varId!, typeNode.text!, `${idNode.text!} : ${typeNode.text!}`]);
            universe.add(typeNode.text!);
          }
        }
      }
    },
    // 处理class声明
    ClassDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children[1];
        universe.add(idNode.text!);
      }
    },
    // 处理函数声明
    FunctionDeclaration(node) {
      if (node.children && node.children.length == 8) {
        const idNode = node.children[1];
        if (node.children[5].kind === "ColonToken") {
          functionEnv.set(idNode.text!, node.children[6].text!);
          universe.add(node.children[6].text!);
        }
      }
    },
    // 处理函数参数
    Parameter(node) {
      if (node.children && node.children.length >= 3) {
        const idNode = node.children[0];
        if (node.children[1].kind === "ColonToken") {
          const typeNode = node.children[2];
          if (typeNode.varId !== undefined) {
            constraints.push(["sameType", idNode.varId!, typeNode.text!, `${idNode.text!} : ${typeNode.text!}`]);
            typeEnv.set(idNode.text!, idNode.varId!);
            universe.add(typeNode.text!);
          }
        }
      }
    },
    // 处理函数调用
    CallExpression(node) {
      if (node.children && node.children.length == 4) {
        const callee = node.children[0];
        if (callee.varId !== undefined && callee.text) {
          const funcType = functionEnv.get(callee.text);
          if (funcType) {
            constraints.push(["sameType", node.varId!, funcType, `call ${callee.text!}`]);
          }
        }
      }
    },
  };

  function processNode(node: AstNode) {
    const id = getTypeVarId(node);

    node.childVarIds = [];

    if (node.children) {
      for (const child of node.children) {
        processNode(child);
        node.childVarIds.push(child.varId!);
      }
    }

    vars[id] = {
      kind: node.kind,
      text: node.text,
      childVarIds: node.childVarIds,
    };

    const handler = handlers[node.kind];
    if (handler) handler(node);
  }

  processNode(astRoot);

  const output = {
    vars,
    universe: Array.from(universe),
    constraints,
    typeEnv: Object.fromEntries(typeEnv.entries()),
    functionEnv: Object.fromEntries(functionEnv.entries()),
  };

  const outputDirPath = path.dirname(outputFile);
  if (!fs.existsSync(outputDirPath)) {
    fs.mkdirSync(outputDirPath, { recursive: true });
  }

  fs.writeFileSync(outputFile, JSON.stringify(output, null, 2), "utf8");
  console.log(`Processed: ${path.basename(inputFile)} → ${path.basename(outputFile)}`);
}

// 主流程
function main() {
  const astFiles = getAstFiles(inputDir);
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }

  for (const astFile of astFiles) {
    const relative = path.relative(inputDir, astFile);
    const outFileName = relative.replace(/\.ast\.json$/, ".constraints.json");
    const outputPath = path.join(outputDir, outFileName);
    processAstFile(astFile, outputPath);
  }
}

main();
