import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";

// 命令行参数解析
const program = new Command();
program
  .requiredOption("-i, --input <inputDir>", "Input AST JSON directory")
  .option("-o, --output <outputDir>", "Output directory (default: ./output)");
program.parse(process.argv);

const options = program.opts();
const inputDir = path.resolve(options.input);
const outputDir = options.output ? path.resolve(options.output) : path.resolve("./output");

// Type 类型
type Type =
  | { kind: "primitive"; name: string }
  | { kind: "array"; elementType: Type }
  | { kind: "function"; params: Param[]; returnType: Type }
  | { kind: "union"; types: Type[] }
  | { kind: "object"; properties: Record<string, Type> }
  | { kind: "unknown" };

interface Param {
  name: string;
  type: Type;
}

// AST 节点类型
interface AstNode {
  kind: string;
  text?: string;
  children?: AstNode[];
  varId?: number;
  position?: { start: { line: number; character: number }; end: { line: number; character: number } };
}

// 全局结构
let typeVarCounter = 1;
const fileToAst: Record<string, AstNode> = {};
const globalExportMap: Record<string, Record<string, number>> = {};
const allNodes: Record<number, { kind: string; text?: string; file?: string; position?: any }> = {};
const allConstraints: Array<[string, number, number | string, string]> = [];
const globalTypeEnv = new Map<string, number>();
const globalFunctionEnv = new Map<string, string>();
const universe = new Set<string>();
const graph: Record<number, Record<number, string>> = {};
const typeSet: Record<number, Set<string>> = {};
const property: Record<string, Record<string, string>> = {};
const parent: Record<number, number> = {};

function getTypeVarId(node: AstNode): number {
  if (node.varId !== undefined) return node.varId;
  const id = typeVarCounter++;
  node.varId = id;
  return id;
}

function findNodesByKind(root: AstNode, kind: string): AstNode[] {
  const found: AstNode[] = [];

  function walk(n: AstNode) {
    if (n.kind === kind) {
      found.push(n);
    }
    if (n.children) {
      for (const child of n.children) {
        walk(child);
      }
    }
  }

  walk(root);

  return found;
}

// 递归打印类型
function printType(t: Type): string {
  switch (t.kind) {
    case "primitive":
      return t.name;
    case "array":
      return printType(t.elementType) + "[]";
    case "function":
      const paramsStr = t.params.map(p => `${p.name}: ${printType(p.type)}`).join(", ");
      return `(${paramsStr}) => ${printType(t.returnType)}`;
    case "object":
      const propsStr = Object.entries(t.properties)
        .map(([k, v]) => `${k}: ${printType(v)}`)
        .join("; ");
      return `{ ${propsStr} }`;
    case "union":
      return t.types.map(printType).join(" | ");
    case "unknown":
      return "unknown";
  }
}

// 第一遍：标号并提取export
function firstPass(filePath: string, ast: AstNode) {
  function walk(node: AstNode) {
    node.varId = getTypeVarId(node);
    if (node.children) node.children.forEach(walk);

    // 还原filepath中的_为\\
    let realPath = path.basename(filePath).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");

    // export Class
    if (node.kind === "ClassDeclaration" && findNodesByKind(node, "ExportKeyword").length > 0) {
      const idNode = node.children?.find(n => n.kind === "Identifier");
      if (idNode && idNode.text) {
        globalExportMap[realPath] ??= {};
        globalExportMap[realPath][idNode.text] = idNode.varId!;
      }
    }
  }

  walk(ast);
  fileToAst[filePath] = ast;
}

// 第二遍：构建约束
function secondPass(filePath: string, node: AstNode) {
  const typeEnv = new Map<string, number>();

  const preOrderHandlers: Record<string, (node: AstNode) => void> = {
    // 处理函数声明
    FunctionDeclaration(node) {
      if (node.children) {
        const idNode = node.children?.find(n => n.kind === "Identifier");
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        if (index !== undefined && index !== -1 && idNode && idNode.varId !== undefined) {
          const returnTypeNode = node.children![index + 1];
          if (returnTypeNode.text) {
            allConstraints.push(["hasType", idNode.varId!, returnTypeNode.text!, `${idNode.text!} : ${returnTypeNode.text!}`]);
            universe.add(returnTypeNode.text!);
            globalFunctionEnv.set(idNode.text!, returnTypeNode.text!);
            console.log(`Adding function ${idNode.text!} with return type ${returnTypeNode.text!}`);
          }
        }
      }
    },
  }

  const handlers: Record<string, (node: AstNode) => void> = {
    StringLiteral(node) {
      allConstraints.push(["hasType", node.varId!, "string", `${node.text!} ∈ string`]);
      universe.add("string");
    },
    NoSubstitutionTemplateLiteral(node) {
      allConstraints.push(["hasType", node.varId!, "string", `${node.text!} ∈ string`]);  
      universe.add("string");
    },
    // 暂时默认为数字
    FirstLiteralToken(node) {
      allConstraints.push(["hasType", node.varId!, "number", `${node.text! } ∈ number`]);
      universe.add("number");
    },
    NumericLiteral(node) {
      allConstraints.push(["hasType", node.varId!, "number", `${node.text!} ∈ number`]);
      universe.add("number");
    },
    TrueKeyword(node) {
      allConstraints.push(["hasType", node.varId!, "boolean", `${node.text!} ∈ boolean`]);
      universe.add("boolean");
    },
    FalseKeyword(node) {
      allConstraints.push(["hasType", node.varId!, "boolean", `${node.text!} ∈ boolean`]);
      universe.add("boolean");
    },
    NullKeyword(node) {
      allConstraints.push(["hasType", node.varId!, "null", `${node.text!} ∈ null`]);
      universe.add("null");
    },
    BigIntLiteral(node) {
      allConstraints.push(["hasType", node.varId!, "bigint", `${node.text!} ∈ bigint`]);
      universe.add("bigint");
    },
    RegularExpressionLiteral(node) {
      allConstraints.push(["hasType", node.varId!, "RegExp", `${node.text!} ∈ RegExp`]);
      universe.add("RegExp");
    },
    TemplateExpression(node) {
      allConstraints.push(["hasType", node.varId!, "string", `${node.text!} ∈ string`]);
      universe.add("string");
    },
    FirstTemplateToken(node) {
      allConstraints.push(["hasType", node.varId!, "string", `${node.text!} ∈ string`]);
      universe.add("string");
    },
    // 处理一元操作
    PrefixUnaryExpression(node) {
      if (node.children && node.children.length >= 2) {
        const operator = node.children[0];
        const exprNode = node.children[1];
        if (exprNode.varId !== undefined) {
          if (operator.kind === "ExclamationToken") {
            allConstraints.push(["hasType", node.varId!, "boolean", `!${exprNode.text!} ∈ boolean`]);
            allConstraints.push(["refersTo", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
            universe.add("boolean");
          }
        }
      }
      // TODO: 处理其他一元操作
    },
    // 二元操作
    BinaryExpression(node) {
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        // 处理赋值操作
        if (left.varId !== undefined && right.varId !== undefined && operator.kind === "FirstAssignment") {
          allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
          allConstraints.push(["sameType", node.varId!, right.varId, `${node.text!} = ${right.text!}`]);
        }
        // 处理加减乘除模运算
        else if (left.varId !== undefined && right.varId !== undefined && operator.kind === "PlusToken" || operator.kind === "MinusToken" || operator.kind === "AsteriskToken" || operator.kind === "SlashToken" || operator.kind === "PercentToken") {
          allConstraints.push(["equalVal", left.varId!, right.varId!, `${left.text!} == ${right.text!}`]);
          allConstraints.push(["sameType", node.varId!, right.varId!, `${node.text!} = ${right.text!}`]);
          allConstraints.push(["sameType", node.varId!, left.varId!, `${node.text!} == ${left.text!}`]);
        }
        // 处理逻辑运算
        else if (left.varId !== undefined && right.varId !== undefined && (operator.kind === "AmpersandAmpersandToken" || operator.kind === "BarBarToken")) {
          allConstraints.push(["sameType", node.varId!, left.varId!, `${node.text!} = ${left.text!}`]);
          allConstraints.push(["sameType", node.varId!, right.varId!, `${node.text!} = ${right.text!}`]);
        }
        // 处理比较运算
        else if (left.varId !== undefined && right.varId !== undefined && (operator.kind === "LessThanToken" || operator.kind === "GreaterThanToken" || operator.kind === "LessThanEqualsToken" || operator.kind === "GreaterThanEqualsToken" || operator.kind === "EqualsEqualsToken" || operator.kind === "ExclamationEqualsToken" || operator.kind === "EqualsEqualsEqualsToken" || operator.kind === "ExclamationEqualsEqualsToken")) {
          allConstraints.push(["hasType", node.varId!, "boolean", `${node.text!} ∈ boolean`]);
        }
        // TODO: 更多二元运算
      }
    },
    // 处理数组字面量
    ElementAccessExpression(node) {
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const right = node.children[2];
        if (left.varId !== undefined && node.varId !== undefined) {
          allConstraints.push(["arrayElement", node.varId, left.varId, `${left.text!}[${right.text!}]`]);
        }
      }
    },
    // 处理属性访问
    PropertyAccessExpression(node) {
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        // 处理dot运算符
        if (operator.kind === "DotToken" && left.varId !== undefined && right.varId !== undefined) {
          // 处理属性访问
          const propName = right.text;
          if (propName) {
            allConstraints.push(["takeProperty", node.varId!, left.varId!, `${left.text!}.${propName}`]);
          }
        }
      }
    },
    // 变量声明
    VariableDeclaration(node) {
      // example: id [: type] [= x]
      const left = node.children?.find(n => n.kind === "Identifier");
      const colonTokenIndex = node.children?.findIndex(n => n.kind === "ColonToken");
      const firstAssignmentIndex = node.children?.findIndex(n => n.kind === "FirstAssignment");
      if (!left || left.varId === undefined) return;
      typeEnv.set(left.text!, left.varId!);
      // 处理类型注解
      if (colonTokenIndex && colonTokenIndex !== -1) {
        const typeNode = node.children?.[colonTokenIndex + 1];
        if (left.varId !== undefined && typeNode && typeNode?.text) {
          allConstraints.push(["hasType", left.varId, typeNode.text!, `${left.text!} = ${typeNode.text!}`]);
          universe.add(typeNode.text!);
        }
      }
      // 处理赋值操作
      if (firstAssignmentIndex && firstAssignmentIndex !== -1) {
        const right = node.children?.[firstAssignmentIndex + 1];
        if (left.varId !== undefined && right?.varId !== undefined) {
          allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
        }
      }
    },
    // New运算符
    NewExpression(node) {
      if (node.children && node.children.length >= 5) {
        const classNode = node.children[1];
        if (classNode.varId !== undefined) {
          allConstraints.push(["hasType", node.varId!, classNode.text!, `new ${classNode.text!}`]);
          universe.add(classNode.text!);
        }
      }
    },
    // 处理括号表达式
    ParenthesizedExpression(node) {
      if (node.children && node.children.length >= 2) {
        const exprNode = node.children[1];
        if (exprNode.varId !== undefined) {
          allConstraints.push(["sameType", node.varId!, exprNode.varId!, `(${exprNode.text!})`]);
        }
      }
    },
    // 处理非空断言
    NoneNullExpression(node) {
      if (node.children && node.children.length >= 2) {
        const exprNode = node.children[1];
        if (exprNode.varId !== undefined) {
          allConstraints.push(["sameType", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
        }
      }
    },
    // 处理标识符
    Identifier(node) {
      if (node.text) {
        const typeId = typeEnv.get(node.text);
        if (typeId !== undefined) {
          allConstraints.push(["sameID", node.varId!, typeId, `same identifier: ${node.text!}`]);
        }
      }
    },
    // 处理for...of循环
    ForOfStatement(node) {
      if (node.children && node.children.length >= 4) {
        const srcNode = node.children?.filter(n => n.kind === "Identifier")[0];
        const dstNode = findNodesByKind(node, "Identifier")[0];
        if (srcNode && dstNode && srcNode.varId !== undefined && dstNode.varId !== undefined) {
          allConstraints.push(["arrayElement", dstNode.varId, srcNode.varId, `for...of ${srcNode.text!} in ${dstNode.text!}`]);
        }
      }
    },
    // 处理三元表达式
    ConditionalExpression(node) {
      if (node.children && node.children.length >= 5) {
        const condition = node.children[0];
        const trueBranch = node.children[2];
        const falseBranch = node.children[4];
        if (condition.varId !== undefined && trueBranch.varId !== undefined && falseBranch.varId !== undefined) {
          allConstraints.push(["sameType", node.varId!, trueBranch.varId!, `? ${trueBranch.text!} : ${falseBranch.text!}`]);
          allConstraints.push(["sameType", node.varId!, falseBranch.varId!, `? ${trueBranch.text!} : ${falseBranch.text!}`]);
        }
      }
    },
    // 处理接口声明
    InterfaceDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
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
            allConstraints.push(["hasType", idNode.varId!, typeNode.text!, `${idNode.text!} : ${typeNode.text!}`]);
            universe.add(typeNode.text!);
          }
        }
      }
    },
    // 处理class声明
    ClassDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        universe.add(idNode.text!);
        for (const child of findNodesByKind(node, "PropertyDeclaration")) {
          const propIdNode = child.children?.find(n => n.kind === "Identifier");
          const index = child.children?.findIndex(n => n.kind === "ColonToken");
          if (index !== undefined) {
            const typeNode = child.children![index + 1];
            if (propIdNode && typeNode && propIdNode.varId !== undefined && typeNode.text) {
              universe.add(typeNode.text!);
              property[idNode.text!] ??= {};
              property[idNode.text!][propIdNode.text!] = typeNode.text;
              // console.log(`Adding property ${propIdNode.text!} of type ${typeNode.text!} to class ${idNode.text!}`);  
            }
          }
        }
        for (const child of findNodesByKind(node, "MethodDeclaration")) {
          const methodIdNode = child.children?.find(n => n.kind === "Identifier");
          const index = child.children?.findIndex(n => n.kind === "ColonToken");
          if (index !== undefined) {
            const returnTypeNode = child.children![index + 1];
            if (methodIdNode && returnTypeNode && methodIdNode.varId !== undefined && returnTypeNode.text) {
              universe.add(returnTypeNode.text!);
              property[idNode.text!] ??= {};
              property[idNode.text!][methodIdNode.text!] = returnTypeNode.text;
            }
          }
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
            allConstraints.push(["hasType", idNode.varId!, typeNode.text!, `${idNode.text!} : ${typeNode.text!}`]);
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
          const funcType = globalFunctionEnv.get(callee.text);
          if (funcType) {
            allConstraints.push(["hasType", node.varId!, funcType, `call ${callee.text!}`]);
          }
          allConstraints.push(["sameType", node.varId!, callee.varId!, `call ${callee.text!}`]);
        }
      }
    },
    // 处理类型断言
    AsExpression(node) {
      if (node.children && node.children.length >= 3) {
        const exprNode = node.children[0];
        const typeNode = node.children[2];
        if (exprNode.varId !== undefined && node.varId !== undefined && typeNode.text) {
          allConstraints.push(["sameType", node.varId!, exprNode.varId!, `${exprNode.text!} as ${typeNode.text!}`]);
          universe.add(typeNode.text!);
          // TODO: 添加类型断言约束
        }
      }
    },
    // 处理import声明
    ImportDeclaration(node) {
      const imported: AstNode[] = findNodesByKind(node, "Identifier");
    
      const raw = node.children?.find(n => n.kind === "StringLiteral")?.text;
      const moduleSpecifier = raw?.replace(/^['"]|['"]$/g, "");  // 去掉引号
      if (!moduleSpecifier) {
        console.warn(`ImportDeclaration in ${filePath} has no moduleSpecifier`);
        return;
      }
    
      const resolvedFile = resolveImportPath(filePath, moduleSpecifier);    
      for (const idNode of imported) {
        const symbol = idNode.text!;
        typeEnv.set(symbol, idNode.varId!);
        if (!resolvedFile) {
          // console.warn(`can not resolve import ${moduleSpecifier} in ${filePath}`);
          allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
          continue;
        }
        const target = globalExportMap[resolvedFile]?.[symbol];
        if (target !== undefined) {
          allConstraints.push(["sameType", idNode.varId!, target, `import ${symbol} from ${moduleSpecifier}`]);
        } else {
          // console.warn(`Symbol ${symbol} not found in export map of ${resolvedFile} in ${filePath}`);
          allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
        }
      }
    }
  };

  // 解析导入路径
  function resolveImportPath(currentFilePath: string, importSpecifier: string): string | undefined {
    if (importSpecifier.startsWith(".")) {
      // 本地模块：相对路径 + 补后缀
      const realCurrentPath = path.basename(currentFilePath).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");
      const absbase = path.resolve(path.dirname(realCurrentPath), importSpecifier);
      const base = path.relative(process.cwd(), absbase);
      const extname = path.extname(realCurrentPath);
      const ret = base + extname;
      return ret;
    } else {
      // 外部模块 or 内建模块
      // console.log(`Resolving external import: ${importSpecifier} in ${currentFilePath}`);
      try {
        return require.resolve(importSpecifier, { paths: [path.dirname(currentFilePath)] });
      } catch {
        return undefined;
      }
    }
  }  

  function walk(node: AstNode) {
    const id = node.varId;
    if (id === undefined) throw new Error("Missing varId in second pass");
    allNodes[id] = { kind: node.kind, text: node.text, file: filePath, position: node.position };

    // 处理先序遍历
    let handler = preOrderHandlers[node.kind];
    if (handler) handler(node);

    if (node.children) node.children.forEach(walk);

    // 处理后序遍历
    handler = handlers[node.kind];
    if (handler) handler(node);
  }

  walk(node);


  for (const [name, id] of typeEnv.entries()) {
    if (!globalTypeEnv.has(name)) {
      globalTypeEnv.set(name, id);
    } else {
      // 如果已经存在，合并类型
      const existingId = globalTypeEnv.get(name)!;
      allConstraints.push(["sameType", id, existingId, `merge type for ${name}`]);
    }
  }
}

// 求解类型图
function deriveVariableTypes() {
  for (let [kind, a, b] of allConstraints) {
    a = find(Number(a));
    if (kind === "sameType" && typeof a === "number" && typeof b === "number") {
      b = find(Number(b));
      graph[b] ??= {}; graph[b][a] = "sameType";
    }
    if (kind === "arrayElement" && typeof a === "number" && typeof b === "number") {
      b = find(Number(b));
      graph[b] ??= {}; graph[b][a] = "arrayElement";
    }
    if (kind === "takeProperty" && typeof a === "number" && typeof b === "number") {
      b = find(Number(b));
      graph[b] ??= {}; graph[b][a] = "takeProperty";
    }
    if (kind === "hasType" && typeof a === "number" && typeof b === "string") {
      if (allNodes[a].kind === "Identifier") {
        graph[a] ??= {};
      }
      typeSet[a] ??= new Set();
      typeSet[a].add(b);
    }
  }

  const worklist = Object.keys(typeSet).map(Number);
  while (worklist.length > 0) {
    const cur = worklist.pop()!;
    const tSet = typeSet[cur] ?? new Set();
    for (const nextStr in graph[cur] || []) {
      const next = Number(nextStr);
      const nSet = typeSet[next] ?? new Set();
      const before = nSet.size;
      if (graph[cur][next] === "sameType") {
        // 如果是同类型，直接合并
        for (const t of tSet) nSet.add(t);
      }
      else if (graph[cur][next] === "takeProperty") {
        // 如果是取属性，添加属性类型
        for (const t of tSet) {
          const propName = allNodes[next]?.text!.split(".").pop();
          // console.log(`Processing property ${propName} for type ${t} in node ${next}`);
          if (propName && property[t] && propName in property[t]) {
            nSet.add(property[t][propName]);
            // console.log(`Adding property type ${property[t][propName]} for ${propName} in node ${next}`);
          }
        }
      }
      else if (graph[cur][next] === "arrayElement") {
        // 去掉数组括号
        for (const t of tSet) {
          if (t.endsWith("[]")) {
            nSet.add(t.slice(0, -2)); // 去掉数组括号
          }
        }
      }
      if (nSet.size > before) {
        typeSet[next] = nSet;
        worklist.push(next);
      }
    }
  }

  const result: Record<string, string> = {};
  for (const [name, id] of globalTypeEnv.entries()) {
    result[name] = [...(typeSet[id] ?? new Set(["unknown"]))].sort().join(" | ");
  }
  return result;
}

function find(x: number): number {
  if (parent[x] === undefined) return x;
  if (parent[x] !== x) parent[x] = find(parent[x]);
  return parent[x];
}

function union(x: number, y: number) {
  const rootX = find(x);
  const rootY = find(y);
  if (rootX !== rootY) {
    parent[rootX] = rootY;
  }
}

// 合并标识符
function mergeIdentifiers() {
  for (const [kind, a, b] of allConstraints) {
    if (kind === "sameID" && typeof a === "number" && typeof b === "number") {
      // 合并标识符
      union(a, b);
    }
  }
}

// 输出图和约束
function emitGlobalTypeGraphAndConstraints() {
  const types = deriveVariableTypes();

  const outDir = path.join(outputDir, "typegraph");
  fs.mkdirSync(outDir, { recursive: true });

  // 写出 constraints 和推理类型
  const constraintOut = path.join(outDir, "constraints.json");
  fs.writeFileSync(
    constraintOut,
    JSON.stringify({ allConstraints, types }, null, 2),
    "utf8"
  );

  // 写出类型图（仅 JSON）
  const jsonGraph = generateTypeGraphJson();
  const jsonOut = path.join(outDir, "typegraph.json");
  fs.writeFileSync(jsonOut, JSON.stringify(jsonGraph, null, 2), "utf8");

  console.log(`Done. Output written to ${outDir}`);

  // ===== JSON 图生成函数 =====
  function generateTypeGraphJson(): { nodes: any[]; edges: any[] } {
    const nodes: any[] = [];
    const edges: any[] = [];
    const seen = new Set<number>();

    for (const [src, dsts] of Object.entries(graph)) {
      const srcId = Number(src);
      const srcVar = allNodes[srcId];
      const srcfile = allNodes[srcId]?.file || "unknown";
      if (!seen.has(srcId)) {
        nodes.push({
          id: srcId,
          label: srcVar?.text || `var_${srcId}`,
          type: typeSet[srcId] ? [...typeSet[srcId]].sort().join(" | ") : "unknown",
          text: srcVar?.text,
          file: srcfile,
          position: srcVar?.position,
          title: `Types: ${[...(typeSet[srcId] ?? [])].sort().join(" | ")}\nText: ${srcVar?.text}\nPos: ${JSON.stringify(srcVar?.position)}`
        });
        seen.add(srcId);
      }

      for (const dstIdStr in dsts) {
        const dstId = Number(dstIdStr);
        const dstVar = allNodes[dstId];
        const dstfile = allNodes[dstId]?.file || "unknown";
        if (!seen.has(dstId)) {
          nodes.push({
            id: dstId,
            label: dstVar?.text || `var_${dstId}`,
            type: typeSet[dstId] ? [...typeSet[dstId]].sort().join(" | ") : "unknown",
            text: dstVar?.text,
            file: dstfile,
            position: dstVar?.position,
            title: `Types: ${[...(typeSet[dstId] ?? [])].sort().join(" | ")}\nText: ${dstVar?.text}\nPos: ${JSON.stringify(dstVar?.position)}`
          });
          seen.add(dstId);
        }

        edges.push({ from: srcId, to: dstId, label: dsts[dstIdStr]});
      }
    }

    return { nodes, edges };
  }
}


// 主流程
function main() {
  const astFiles = getAstFiles(inputDir);
  for (const file of astFiles) {
    const ast = JSON.parse(fs.readFileSync(file, "utf8"));
    firstPass(file, ast);
  }
  // 控制台输出globalExportMap
  console.log("Global Export Map:", JSON.stringify(globalExportMap, null, 2));
  for (const file of astFiles) {
    secondPass(file, fileToAst[file]);
  }
  // 创建一个虚拟节点，表示未知的导入
  allNodes[0] = { kind: "null", text: "unknown import hole", file: "null", position: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } } };
  mergeIdentifiers();
  emitGlobalTypeGraphAndConstraints();
}

// 递归获取所有 AST 文件
function getAstFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let files: string[] = [];
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) files = files.concat(getAstFiles(fullPath));
    else if (entry.name.endsWith(".ast.json")) files.push(fullPath);
  }
  return files;
}

main();
