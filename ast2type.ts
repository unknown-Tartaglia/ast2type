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
const outputDir = options.output ? path.resolve(options.output) : path.resolve("./output");

interface AstNode {
  kind: string;
  text?: string;
  children?: AstNode[];
  varId?: number;
  position?: { start: { line: number; character: number }; end: { line: number; character: number } }; // 添加 position 属性
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

function processAstFile(inputFile: string, outputPath: string, outFileName: string) {
  const astRoot: AstNode = JSON.parse(fs.readFileSync(inputFile, "utf8"));

  let typeVarCounter = 0;
  const vars: Record<number,
  { 
    kind: string; 
    text?: string; 
    position?: 
    { 
      start: { line: number; character: number };
      end: { line: number; character: number }
    } }> = {};
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
      if (node.children && node.children.length >= 3) {
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
          constraints.push(["sameType", node.varId!, left.varId, `${node.text!} == ${left.text!}`]);
        }
      }
    },
    // 变量声明
    VariableDeclaration(node) {
      // example: id [: type] = x
      if (node.children && node.children.length >= 3) {
        const left = node.children![0];
        if (node.children![1].text == ":" && node.children.length >= 5) {
          // 处理带类型注解初始化
          if (left.varId !== undefined && node.children![2].varId !== undefined) {
            constraints.push(["hasType", left.varId, node.children![2].text!, `${left.text!} = ${node.children![2].text!}`]);
            constraints.push(["sameType", left.varId, node.children![4].varId!, `${left.text!} == ${node.children![4].text!}`]);
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
          constraints.push(["hasType", node.varId!, classNode.text!, `new ${classNode.text!}`]);
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
            constraints.push(["hasType", idNode.varId!, typeNode.text!, `${idNode.text!} : ${typeNode.text!}`]);
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
            constraints.push(["hasType", idNode.varId!, typeNode.text!, `${idNode.text!} : ${typeNode.text!}`]);
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
            constraints.push(["hasType", node.varId!, funcType, `call ${callee.text!}`]);
          }
        }
      }
    },
  };

  function processNode(node: AstNode) {
    const id = getTypeVarId(node);

    if (node.children) {
      for (const child of node.children) {
        processNode(child);
      }
    }

    vars[id] = {
      kind: node.kind,
      text: node.text,
      position: node.position,
    };

    const handler = handlers[node.kind];
    if (handler) handler(node);
  }

  // 处理节点并输出约束信息
  processNode(astRoot);

  const output = {
    vars,
    universe: Array.from(universe),
    constraints,
    typeEnv: Object.fromEntries(typeEnv.entries()),
    functionEnv: Object.fromEntries(functionEnv.entries()),
    variableTypes: deriveVariableTypes(),
  };

  const outputFile = path.join(outputPath + "/constraint/", outFileName + ".constraints.json");
  const outputDirPath = path.dirname(outputFile);
  if (!fs.existsSync(outputDirPath)) {
    fs.mkdirSync(outputDirPath, { recursive: true });
  }

  fs.writeFileSync(outputFile, JSON.stringify(output, null, 2), "utf8");
  console.log(`Processed: ${path.basename(inputFile)} → ${path.basename(outputFile)}`);

  // 类型约束传播求解
  function deriveVariableTypes(): Record<string, string> {
    const typeGraph: Record<number, number[]> = {};
    const typeSet: Record<number, Set<string>> = {};

    for (const [kind, a, b] of constraints) {
      if (kind === "sameType" && typeof b === "number" && typeof a === "number") {
        if (!typeGraph[a]) typeGraph[a] = [];
        if (!typeGraph[b]) typeGraph[b] = [];
        typeGraph[b].push(a);
      }
    }

    for (const [kind, v, t] of constraints) {
      if (kind === "hasType" && typeof t === "string") {
        if (!typeSet[v]) typeSet[v] = new Set();
        typeSet[v].add(t);
      }
    }

    const worklist = Object.keys(typeSet).map(x => Number(x));

    while (worklist.length > 0) {
      const cur = worklist.pop()!;
      const curTypes = typeSet[cur] ?? new Set();
      for (const next of typeGraph[cur] || []) {
        const key = `${cur}->${next}`;
        const nextSet = typeSet[next] ?? new Set();
        const sizeBefore = nextSet.size;
        for (const t of curTypes) nextSet.add(t);
        if (nextSet.size > sizeBefore) {
          typeSet[next] = nextSet;
          worklist.push(next);
        }
      }
    }

    for (const [kind, a, b] of constraints) {
      if (kind === "equalVal" && typeof b === "number") {
        const t1 = typeSet[a] ?? new Set();
        const t2 = typeSet[b] ?? new Set();
        const intersection = [...t1].filter(x => t2.has(x));
        if (intersection.length === 0 && t1.size > 0 && t2.size > 0) {
          console.warn(`Validation failed for ${vars[a].text} and ${vars[b].text}: no common types found:\n  - ${Array.from(t1).sort().join(", ")}\n  - ${Array.from(t2).sort().join(", ")}`);
        }
      }
    }

    // 生成 DOT 格式图
    function generateTypeGraphDot(): string {
      let dot = "digraph TypeGraph {\n  node [shape=box];\n";

      let nodes = new Set<number>();
      for (const [src, dsts] of Object.entries(typeGraph)) {
          nodes.add(Number(src));
          for (const dst in dsts) {
            nodes.add(Number(dst))
          }
      }
      for (const [varId, types] of Object.entries(typeSet)) {
        nodes.add(Number(varId));
      }

      for (const node of nodes) {
        const varName = vars[node].text && vars[node].text.length < 20 ? vars[node].text.replace(/\"/g, "\\\"") : `${node}`;
        if (!vars[node].text) {
          console.log(`No text for node ${node}`);
        } else if (vars[node].text.length >= 20) {
          console.log(`Long text for node ${node}: ${vars[node].text}`);
        }
        const types = typeSet[node];
        const typeStr = types ? [...types].sort().join(" | ") : "unknown";
        const v = vars[node];
        const pos = v ? v.position
          ? `(${v.position.start.line}:${v.position.start.character} - ${v.position.end.line}:${v.position.end.character})`
          : "(no pos)" : "(no var)";
        const label = `${varName}\\n${pos}\\n${typeStr}`;

        dot += `  "${node}" [label="${label}"];\n`;
      }

      for (const [kind, a, b] of constraints) {
        if (kind === "sameType" && typeof b === "number") {
          dot += `  "${b}" -> "${a}";\n`;
        }
      }

      dot += "}\n";
      return dot;
    }

    // 写入文件
    const outputFile = path.join(outputPath + "/dotfile/", outFileName + ".typegraph.dot");
    const outputDirPath = path.dirname(outputFile);
    if (!fs.existsSync(outputDirPath)) {
      fs.mkdirSync(outputDirPath, { recursive: true });
    }
    
    const dotContent = generateTypeGraphDot();
    fs.writeFileSync(outputFile, dotContent, "utf8");

    const result: Record<string, string> = {};
    for (const [varName, varId] of typeEnv.entries()) {
      const types = typeSet[varId];
      result[varName] = types ? [...types].sort().join(" | ") : "unknown";
    }
    return result;
  }
}

// 主流程
function main() {
  const astFiles = getAstFiles(inputDir);
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }

  for (const astFile of astFiles) {
    const relative = path.relative(inputDir, astFile);
    const outFileName = relative.replace(/\.ast\.json$/, "");
    processAstFile(astFile, outputDir, outFileName);
  }
}

main();
