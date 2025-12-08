import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";
import { get } from "http";
import { ts } from "ts-morph";
import { serialize } from "v8";

// 命令行参数解析
const program = new Command();
program
  .requiredOption("-i, --input <inputDir>", "Input AST JSON directory")
  .option("-o, --output <outputDir>", "Output directory (default: ./output)");
program.parse(process.argv);

const options = program.opts();
const inputDir = path.resolve(options.input);
const outputDir = options.output ? path.resolve(options.output) : path.resolve("./output");

const LOG_SCOPE = false; // 是否开启日志作用域
const LOG_TYPENODE = false; // 是否开启类型节点日志
const LOG_TYPENODE_VERBOSE = false; // 是否开启类型节点详细日志
const LOG_IDENTIFIER_NODE = false; // 是否开启标识符节点日志
const LOG_IMPORT = false; // 是否开启导入日志
const LOG_TYPE_FLOW = true; // 是否开启类型流日志

const DEDUCE_ONLY_WHEN_ALL_KNOWNN = false; // 仅在所有分支类型已知时进行类型推断

// 常量类型
const NUMBER = 1;
const STRING = 2;
const BOOLEAN = 3;
const ANY = 4;
const UNKNOWN = 5;
const VOID = 6;
const NULL = 7;
const UNDEFINED = 8;
const NEVER = 9;
const REGEXP = 10;
const BIGINT = 11;

interface Param {
  name: string;
  type: number;
}

// Type 类型结构体
type TypeNode =
  | { kind: "primitive"; name: string }
  | { kind: "array"; elementType: number }
  | { kind: "function"; name: string; id: number; params: Param[]; returnType: number }
  | { kind: "union"; types: number[] }
  | { kind: "object"; name: string; id: number; properties: Record<string, number> }
  | { kind: "enum"; name: string; members: Record<string, number> };


// 反向映射：序列化 TypeNode → ID 确保唯一性
const typeNodeReverseMap = new Map<string, number>();

// AST 节点类型
interface AstNode {
  kind: string;
  text?: string;
  parent?: AstNode;
  children?: AstNode[];
  varId?: number;
  position?: { start: { line: number; character: number }; end: { line: number; character: number } };
  offset?: number;
}

// 全局结构
let typeVarCounter = 100;
const cnt: Record<number, number> = {};
const fileToAst: Record<string, AstNode> = {};
const globalExportMap: Record<string, Record<string, number>> = {};
const globalExportFa: Record<string, Record<string, string[]>> = {};
const syntaxNodes: Record<number, { kind: string; text?: string; file?: string; position?: any; offset?: number; v8kind?:string; context?:string }> = {};
const typeNodes: Map<number, TypeNode> = new Map();
const allConstraints: Array<[string, number, number, string]> = [];
const globalVarBindings = new Map<string, number>();
const graph: Map<number, Map<number, string>> = new Map();
const source: Map<number, Map<number, number>> = new Map();
const typeSet: Map<number, number> = new Map();
const parent: Record<number, number> = {};
const globalImportMap: Map<string, string> = new Map((() => { try { return JSON.parse(fs.readFileSync(path.join(inputDir, "importMap.json"), "utf8")); } catch { return []; } })());
let worklist: number[] = [];
const funcParam: Record<number, number[]> = {};
const constructors: Record<number, number> = {};
const tsMorphNodes = ["BigIntLiteral", "NumericLiteral", "FirstLiteralToken", "NullKeyword", "TrueKeyword", "FalseKeyword", "ObjectLiteralExpression",
  "ArrayLiteralExpression", "BinaryExpression", "PrefixUnaryExpression", "PostfixUnaryExpression", "TypeOfExpression", "RegularExpressionLiteral",
  "VoidExpression", "Identifier", "ThisKeyword", "ConditionalExpression", "PropertyAccessExpression", "ElementAccessExpression", "CallExpression",
  "ArrowFunction", "FunctionExpression", "ReturnStatement", "ParenthesizedExpression", "TemplateExpression", "NewExpression"];
const v8Nodes = ["Literal", "ObjectLiteral", "ArrayLiteral", "BinaryOperation", "UnaryOperation", "CountOperation", "RegExpLiteral", "VariableProxy", 
  "Conditional", "Property", "Call", "FunctionLiteral", "ReturnStatement", "TemplateLiteral", "CallNew"];
const start = Date.now();
const console_methods = ["log", "error", "warn", "info"] as const;

// 返回[h:m:s]
function getTimeElapsed(): string {
  const elapsed = Date.now() - start;

  const h = Math.floor(elapsed / 3600000);
  const m = Math.floor((elapsed % 3600000) / 60000);
  const s = Math.floor((elapsed % 60000) / 1000);

  // 补零函数
  const pad = (n: number) => n.toString().padStart(2, "0");

  return `[${pad(h)}:${pad(m)}:${pad(s)}] `;
}

for (const m of console_methods) {
  const original = console[m];

  console[m] = (...args: any[]) => {
    original(getTimeElapsed(), ...args);
  };
}

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

function findParentByKind(root: AstNode | undefined, kind: string): AstNode | undefined {
  if (!root) return undefined;
  if (root.kind === kind) return root;
  return findParentByKind(root.parent, kind);
}

// 递归打印类型
function printType(n: number): string {
  const occur: Record<string, number> = {};
  return helper(n);
  function helper(n: number): string {
    const t = typeNodes.get(n);
    if (!t) {
      // if (LOG_TYPENODE)
        console.warn(`Type ID ${n} not found in typeNodes`);
      return "impossible! type unknown in printType";
    }
    switch (t.kind) {
      case "primitive":
        return t.name;
      case "array":
        return helper(t.elementType) + "[]";
      case "function":
        // const paramsStr = t.params.map(p => `${p.name}: ${helper(p.type)}`).join(", ");
        // return `(${paramsStr}) => ${helper(t.returnType)}`;
        return `function:${t.name}[${t.id}]`;
      case "object":
        return `object:${t.name}[${t.id}]`;
      case "union":
        return t.types.map(helper).join(" | ");
      case "enum":
        return `enum ${t.name} { ${Object.entries(t.members).sort().map(([k, v]) => `${k}=${v}`).join(",")} }`;
    }
  }
}

// 打印完整类型
function printFullType(n: number): string {
  const occur: Record<string, number> = {};
  return helper(n);
  function helper(n: number): string {
    const t = typeNodes.get(n);
    if (!t) {
      // if (LOG_TYPENODE)
        console.warn(`Type ID ${n} not found in typeNodes`);
      return "impossible! type unknown in printFullType";
    }
    switch (t.kind) {
      case "primitive":
        return t.name;
      case "array":
        return helper(t.elementType) + "[]";
      case "function":
        if (occur[t.id]) {
          return `function:${t.name}`;
        }
        occur[t.id] = n;

        const paramsStr = t.params.map(p => `${p.name}: ${helper(p.type)}`).join(", ");
        return `(${paramsStr}) => ${helper(t.returnType)}`;
      case "object":
        if (occur[t.id]) {
          return `object:${t.name}`;
        }
        occur[t.id] = n;
        const propsStr = Object.entries(t.properties)
          .map(([k, v]) => `${k}: ${helper(v)}`)
          .join("; ");
        return `{ ${t.name} | ${propsStr} }`;
      case "union":
        return t.types.map(helper).join(" | ");
      case "enum":
        return `enum ${t.name} { ${Object.entries(t.members).sort().map(([k, v]) => `${k}=${v}`).join(",")} }`;
    }
  }
}


function printJsonType(typeId: number): any {
  const node = typeNodes.get(typeId);
  if (!node) return "unknown";

  switch (node.kind) {
    case "primitive":
      return node.name;
    case "union":
      return Array.from(new Set(node.types.map(t => printJsonType(t))));
    case "array":
      return `array`;
    case "object":
      return "object";
    case "enum":
      return "enum";
    case "function":
      return "function"
    default:
      return "unknown"
  }
}



// 序列化 TypeNode 为字符串, 确保唯一性
const hash : Map<TypeNode, string> = new Map();
function serializeTypeNode(t: TypeNode): string {
  if (!t) {
    // if (LOG_TYPENODE)
      console.warn(`illegal typeNode ${JSON.stringify(t)}`);
    return "illegal typeNode";
  }
  if (hash.has(t)) {
    return hash.get(t)!;
  }
  let ret;
  switch (t.kind) {
    case "primitive":
      ret = `primitive:${t.name}`;
      break;
    case "array":
      ret = `array:${t.elementType}`;
      break;
    case "function":
      ret = `function ${t.id}:${t.params.sort().map(p => `${p.name}:${p.type}`).join(",")}->${t.returnType}`;
      break;
    case "union":
      ret = `union:${t.types.sort().join("|")}`;
      break;
    case "object":
      ret = `object:{${t.id}:${Object.entries(t.properties).sort().map(([k, v]) => `${k}:${v}`).join(",")}}`;
      break;
    case "enum":
      ret = `enum:{${t.name}:${Object.entries(t.members).sort().map(([k, v]) => `${k}=${v}`).join(",")}}`;
  }
  hash.set(t, ret);
  return ret;
}

// 反向索引：typeNodeId -> Set<typeVarId>
const typeNodeUsers: Map<number, Set<number>> = new Map();
function setTypeVar(vid : number, tid : number) {
  typeSet.set(vid, tid);
  typeNodeUsers.set(tid, (typeNodeUsers.get(tid) ?? new Set()).add(vid));
}

function newTypeNode(ty: TypeNode): number{
  if (LOG_TYPENODE_VERBOSE)
    console.log(`allocating new type node: ${JSON.stringify(ty)} ~~~ ${serializeTypeNode(ty)}`);
  let serialized = serializeTypeNode(ty);
  if (typeNodeReverseMap.has(serialized)) {
    const id = typeNodeReverseMap.get(serialized);
    return id!;
  }


  // 处理对象类型的循环引用
  const occur: Record<string, number> = Object.create(null);
  return helper(ty);
  function helper(t: TypeNode): number {
    if (!t) {
      // if (LOG_TYPENODE)
        console.warn(`Undefined typeNode in newTypeNode`);
      return UNKNOWN; // 返回UNKNOWN
    }
    if (t.kind === "array") {
      const ret = helper(typeNodes.get(t.elementType)!);
      if (t.elementType !== ret) {
        t.elementType = ret;
      }
    }
    else if (t.kind === "function") {
      if (occur[t.id] !== undefined) {
        occur[t.id] = newTypeNode(t)
        return occur[t.id];
      }
      occur[t.id] = UNKNOWN;

      for (const param of t.params) {
        const ret = helper(typeNodes.get(param.type)!);
        if (param.type !== ret) {
          param.type = ret;
        }
      }
      const returnType = helper(typeNodes.get(t.returnType)!);
      if (t.returnType !== returnType) {
        t.returnType = returnType;
      }

      if (occur[t.id] !== UNKNOWN && serializeTypeNode(typeNodes.get(occur[t.id])!) !== serializeTypeNode(t)) {
        // 修改TypeNode，危险操作，传播影响
        if (LOG_TYPENODE) {
          console.log(`Change type node ${occur[t.id]} from ${JSON.stringify(typeNodes.get(occur[t.id])!) } to ${JSON.stringify(t)}`);
        }
        typeNodes.set(occur[t.id], t);
        typeNodeReverseMap.set(serializeTypeNode(t), occur[t.id]);
        for (const [id, val] of typeSet)
          if (val === occur[t.id])
            worklist.push(id);
        return occur[t.id];
      }
    } else if (t.kind === "union") {
      const newTypes = t.types.map(ty => helper(typeNodes.get(ty)!));
      t.types = newTypes;
    } else if (t.kind === "object") {
      // console.log(`enter ${t.name}`)
      if (occur[t.id]) {
        occur[t.id] = newTypeNode(t)
        return occur[t.id];
      }
      occur[t.id] = UNKNOWN;

      for (const key in t.properties) {
        const ret = helper(typeNodes.get(t.properties[key])!);
        if (t.properties[key] !== ret) {
          t.properties[key] = ret;
        }
      }

      if (occur[t.id] !== UNKNOWN && serializeTypeNode(typeNodes.get(occur[t.id])!) !== serializeTypeNode(t)) {
        // 修改TypeNode，危险操作，传播影响
        if (LOG_TYPENODE) {
          console.log(`Change type node ${occur[t.id]} from ${JSON.stringify(typeNodes.get(occur[t.id])!) } to ${JSON.stringify(t)}`);
        }
        typeNodes.set(occur[t.id], t);
        typeNodeReverseMap.set(serializeTypeNode(t), occur[t.id]);
        const affected = typeNodeUsers.get(occur[t.id]);
        if (affected) {
          for (const id of affected) {
            worklist.push(id);
          }
        }
        return occur[t.id];
      }
      // console.log(`exit ${t.name}`)
      // t.properties = Object.create(null);
    }
    serialized = serializeTypeNode(t);
    if (typeNodeReverseMap.has(serialized)) {
      const id = typeNodeReverseMap.get(serialized)!;
      if (LOG_TYPENODE) {
        console.log(`find in typenode reverse map: ${id} : ${serialized}`);
      }
      return id;
    } else {
      const id = typeVarCounter++;
      typeNodes.set(id, t);
      typeNodeReverseMap.set(serialized, id);
      if (LOG_TYPENODE) {
        console.log(`New type node created: ${id} : ${serialized}`);
      }
      return id;
    }
  }
}

function mergeTypes(tys: number[]) : number {
  let tyList : number[] = [], ret : number;
  for (const ty of tys) {
    const typeNode = typeNodes.get(ty);
    if (typeNode?.kind === "union") 
      tyList = tyList.concat([...typeNode.types]);
    else tyList.push(ty);
  }
  

  tyList = [...new Set(tyList.filter(ty => ty !== UNKNOWN))];


  if (tyList.length === 1) {
    ret = tyList[0];
  } else if (tyList.length > 1) {
    ret = newTypeNode( { kind: "union", types: tyList});
  } else {
    // console.warn(`Trap!!! merge types ${[...tys]} to UNKNOWN`);
    ret = UNKNOWN;
  }
  if (LOG_TYPE_FLOW) 
    console.log(`merge types ${[...tys]} to ${ret}`);
  return ret;
}

// 合并不同分支类型
function mergeBranches(node : number, kinds? : string[]) : number {
  let ret : number;
  if (source.get(node)?.size === 1) {
    const src = source.get(node)!.keys().next().value!;
    if (kinds && !kinds.includes(graph.get(src)?.get(node) ?? "")) {
      console.warn(`Unexpected merge branches when branchNum = 1 && edge ${src}->${node} not in type ${[...kinds]}`);
    }
    ret = source.get(node)?.get(src)!;
  }
  else {
    let tyList : number[] = [];
    for (const src of source.get(node)!.keys()) {
      if (kinds && !kinds.includes(graph.get(src)?.get(node) ?? "") || !kinds && (graph.get(src)?.get(node) ?? "") === "returnType") continue;
      const ty = source.get(node)!.get(src)!;
      const typeNode = typeNodes.get(ty);
      if (typeNode?.kind === "union") 
        tyList = tyList.concat([...typeNode.types]);
      else tyList.push(ty);
    }

    
    const seen = new Map<string, number>();
    let has_unknown = false;
    for (const ty of tyList) {
      if (ty === UNKNOWN) {
        has_unknown = true;
        continue;
      }
      const sig = serializeTypeNode(typeNodes.get(ty)!);
      const old = seen.get(sig);
      if (old === undefined || old < ty) seen.set(sig, ty);
    }
    if (DEDUCE_ONLY_WHEN_ALL_KNOWNN && has_unknown) return UNKNOWN;
    tyList = [...seen.values()];    


    if (tyList.length === 1) {
      ret = tyList[0];
    } else if (tyList.length > 1) {
      ret = newTypeNode( { kind: "union", types: tyList});
    } else {
      ret = UNKNOWN;
    }
  }
  if (LOG_TYPE_FLOW) 
    console.log(`merge branches at ${node} from ${[...source.get(node)?.keys()!]} to ${ret} as ${serializeTypeNode(typeNodes.get(ret)!)}`)
  return ret;
}

function makePurePropertiesCopy(
  base: Record<string, number>,
  extraKey: string,
  extraVal: number
): Record<string, number> {
  const obj = Object.create(null);
  Object.assign(obj, base);
  obj[extraKey] = extraVal;
  return obj;
}

// 第一遍：标号并提取export
function firstPass(filePath: string, ast: AstNode) {
  function walk(node: AstNode) {
    node.varId = getTypeVarId(node);
    // 提前函数声明
    node.children?.sort((a, b) => {
      const aFunc = a.kind === "FunctionDeclaration";
      const bFunc = b.kind === "FunctionDeclaration";
      return (aFunc === bFunc) ? 0 : aFunc ? -1 : 1;
    });
    for (const child of node.children || []) {
      child.parent = node;
      walk(child);
    }

    // 还原filepath中的^为\\
    let realPath = path.basename(filePath).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");

    // export Class Enum TypeAlias Interface
    if ((node.kind === "ClassDeclaration" || node.kind === "InterfaceDeclaration" || node.kind === "EnumDeclaration" || node.kind === "TypeAliasDeclaration" || node.kind === "FunctionDeclaration") && findNodesByKind(node, "ExportKeyword").length > 0) {
      const idNode = node.children?.find(n => n.kind === "Identifier");
      if (idNode && idNode.text) {
        globalExportMap[realPath] ??= {};
        globalExportMap[realPath][idNode.text] = idNode.varId!;
        // 处理default
        const dftkwd = findNodesByKind(node, "DefaultKeyword")[0];
        if (dftkwd) {
          globalExportMap[realPath][dftkwd.text!] = dftkwd.varId!;
          allConstraints.push(["sameType", dftkwd.varId!, idNode.varId!, "default keyword"]);
        }
      }
    }

    // export FirstStatement
    if (node.kind === "FirstStatement" && findNodesByKind(node, "ExportKeyword").length > 0) {
      const dftkwd = findNodesByKind(node.children?.[0]!, "DefaultKeyword")[0];
      const vardcl = node.children?.find(n => n.kind === "VariableDeclarationList")
      if (!vardcl) return;
      const stx = vardcl.children?.find(n => n.kind === "SyntaxList");
      if (!stx) return;
      const idNodes = stx.children?.filter(n => n.kind === "VariableDeclaration");
      if (!idNodes) return;
      if (idNodes.length > 0) {
        globalExportMap[realPath] ??= {};
        for (const idNode of idNodes) 
          if (idNode.children && idNode.children.length > 0 && idNode.children[0].kind === "Identifier" && idNode.children[0].text){
            globalExportMap[realPath][idNode.children[0].text] = idNode.children[0].varId!;
            if (idNode.children.length === 3 && idNode.children[1].kind === "FirstAssignment")
              allConstraints.push(["sameType", idNode.children[0].varId!, idNode.children[2].varId!, `${idNode.text}`])
        }
        // 处理default
        if (dftkwd && idNodes.length === 1) {
          const idNode = idNodes[0];
          if (idNode.children && idNode.children.length > 0 && idNode.children[0].kind === "Identifier" && idNode.children[0].text) {
            globalExportMap[realPath][dftkwd.text!] = dftkwd.varId!;
            allConstraints.push(["sameType", dftkwd.varId!, idNodes[0].varId!, "default keyword"]);
          }
        }
      }
    }

    // exportDeclararion
    if (node.kind === "ExportDeclaration" || node.kind === "ExportAssignment") {
      // 处理default
      if (!node.children) return;
      const dftkwdIdx = node.children?.findIndex(n => n.kind === "DefaultKeyword");
      const dftkwd = dftkwdIdx === -1 ? undefined : node.children?.[dftkwdIdx];
      const idNode = dftkwdIdx === -1 ? node.children?.[1] : node.children?.[2];
      if (idNode.text && idNode.kind === "Identifier") {
        globalExportMap[realPath] ??= {};
        globalExportMap[realPath][idNode.text] = idNode.varId!;
      } else if (idNode.kind === "NamedExports") {
        const idNodes = findNodesByKind(node, "ExportSpecifier");
        if (idNodes.length > 0) {
          globalExportMap[realPath] ??= {};
            for (const idNode of idNodes) {
              if (idNode.children && idNode.children.length === 3 && idNode.children[2].kind === "Identifier" && idNode.children[2].text) {
                globalExportMap[realPath][idNode.children[2].text] = idNode.children[2].varId!;
                allConstraints.push(["sameType", idNode.children[2].varId!, idNode.children[0].varId!, `${idNode.text}`]);
              } else if (idNode.children && idNode.children.length === 1 && idNode.children[0].kind === "Identifier" && idNode.children[0].text) {
                globalExportMap[realPath][idNode.children[0].text] = idNode.children[0].varId!;
              }
          }
        }
      }
      if (dftkwd) {
        globalExportMap[realPath] ??= {};
        globalExportMap[realPath][dftkwd.text!] = dftkwd.varId!;
        allConstraints.push(["sameType", dftkwd.varId!, idNode.varId!, "default keyword"]);
        // TODO: 判断是否只有一个default
      }

      // export xxx from file
      const idx = node.children.findIndex(n => n.kind === "FromKeyword");
      if (idx && idx !== -1) {
        const f = node.children[idx + 1];
        if (!f || !f.text) {
          console.error(`export xxx from no file`);
        } else {
          const dst = resolveImportPath(filePath, f.text.replace(/^['"]|['"]$/g, ""));

          if (dst) {
            if (node.children.find(n => n.kind === "AsterisToken")) {
              globalExportFa[realPath] ??= {};
              globalExportFa[realPath]["*"] ??= [];
              globalExportFa[realPath]["*"].push(dst);
              // console.log(`+++ ${dst} to ${realPath}`)
            }
          }
          if (LOG_IMPORT && !dst)
            console.error(`can not resolve ${f.text} at ${filePath}`);
        }
      }
    }
  }

  walk(ast);
  fileToAst[filePath] = ast;
}

// 第二遍：构建约束
function secondPass(filePath: string, node: AstNode) {
  let scopeStack: Map<string, number>[] = [];
  let varBindings = new Map<string, number>();
  let paramBindings = new Map<string, number>();

  const preOrderHandlers: Record<string, (node: AstNode) => void> = {
    // 处理匿名对象
    ObjectLiteralExpression(node) {
      syntaxNodes[node.varId!].v8kind = "ObjectLiteral"
      const lst = node.children?.find(n => n.kind === "SyntaxList");
      if (lst) {
        const typeId = newTypeNode({ kind: "object", name: `anonymous${node.varId!}`, id: node.varId!, properties: Object.create(null) });
        allConstraints.push(["hasType", node.varId!, typeId, `new object`]);
      }
    },
    // 赋予属性
    PropertyAssignment(node) {
      if (node.children?.length === 3) {
        // 清楚引号
        const idNode = node.children[0].kind === "StringLiteral" ? node.children[0].text?.slice(1, -1) : node.children[0].text;
        if (!idNode) return;
        node.children[2].text = idNode;
        const obj = node.parent?.parent;
        if (!obj || !obj.varId) return;
        allConstraints.push(["initProperty", obj.varId, node.children[2].varId!, idNode!]);
      }
    },
    // 短赋予属性
    ShorthandPropertyAssignment(node) {
      if (node.children) {
        const obj = node.parent?.parent;
        if (!obj || !obj.varId) return;
        allConstraints.push(["initProperty", obj.varId, node.children[0].varId!, node.children[0].text!]);
      }
    },
    // 处理函数声明
    FunctionDeclaration(node) {
      if (node.children) {
        const idNode = node.children?.find(n => n.kind === "Identifier");
        if (idNode && idNode.varId !== undefined && idNode.text) {
          varBindings.set(idNode.text, idNode.varId!);
        }


        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: UNKNOWN });
            setTypeVar(idNode?.varId!, id);
            allConstraints.push(["returnAnnotation", idNode?.varId!, typeNode.varId, `return type of function ${idNode?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: VOID });
          setTypeVar(idNode?.varId!, id);
        }
        else {
          const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: UNKNOWN });
          setTypeVar(idNode?.varId!, id);
        }
      }
    },
    FunctionExpression(node) {
      syntaxNodes[node.varId!].v8kind = "FunctionLiteral";
      if (node.children) {
        const idNode = node;
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: UNKNOWN });
            setTypeVar(idNode?.varId!, id);
            allConstraints.push(["returnAnnotation", idNode?.varId!, typeNode.varId, `return type of function ${idNode?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: idNode?.varId!, params: [], returnType: VOID });
          setTypeVar(idNode?.varId!, id);
        }
        else {
          const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: idNode?.varId!, params: [], returnType: UNKNOWN });
          setTypeVar(idNode?.varId!, id);
        }
      }
    },
    // 变量声明
    VariableDeclaration(node) {
      // example: id [: type] [= x]
      const left = node.children?.[0];
      const colonTokenIndex = node.children?.findIndex(n => n.kind === "ColonToken");
      const firstAssignmentIndex = node.children?.findIndex(n => n.kind === "FirstAssignment");
      if (!left || left.varId === undefined || left.kind !== "Identifier") return;

      let fa = findParentByKind(node, "VariableDeclarationList");
      if (fa && fa.kind === "VariableDeclarationList" && fa.parent && fa.parent.kind === "ForOfStatement") {
        paramBindings.set(left.text!, left.varId!);
      } else {
        if (LOG_IDENTIFIER_NODE)
          console.log(`Variable ${left.text} has ID ${left.varId}`);
        varBindings.set(left.text!, left.varId!);
      }
      // 处理类型注解
      if (colonTokenIndex && colonTokenIndex !== -1) {
        const typeNode = node.children?.[colonTokenIndex + 1];
        if (typeNode && typeNode.varId) {
          allConstraints.push(["annotation", left.varId, typeNode.varId, `annotation ${left.text!} : ${typeNode.text!}`]);
        }
      }
      // 处理赋值操作
      if (firstAssignmentIndex && firstAssignmentIndex !== -1) {
        const right = node.children?.[firstAssignmentIndex + 1];
        syntaxNodes[node.varId!].v8kind = "Assignment";
        syntaxNodes[node.varId!].offset = right?.offset;
        if (left.varId !== undefined && right?.varId !== undefined) {
          allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
        }
      }
    },
    TypeAliasDeclaration(node) {
      const left = node.children?.find(n => n.kind === "Identifier");
      const right = node.children?.find(n => n.kind === "TypeReference");
      if (!left || !right || !left.varId || !right.varId) return;
      if (LOG_IDENTIFIER_NODE)
        console.log(`Variable ${left.text} has ID ${left.varId}`);
      varBindings.set(left.text!, left.varId);
      allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);

      //处理namespace
      let paNode = node.parent?.parent?.parent;
      if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
      paNode = paNode.children?.find(n => n.kind === "Identifier");
      if (!paNode) return;
      allConstraints.push(["initProperty", paNode.varId!, left.varId!, `${paNode.text!}.${left.text!}`]);
      allConstraints.push(["takeProperty", left.varId!, paNode.varId!, `${paNode.text!}.${left.text!}`]);
    },
    // 处理函数参数
    Parameter(node) {
      if (node.children) {
        const paramIdNode = node.children?.find(n => n.kind === "Identifier");
        if (!paramIdNode || !paramIdNode.varId) return;
        paramBindings.set(paramIdNode.text!, paramIdNode.varId!);

        // 处理类型注解
        const colonIndex = node.children?.findIndex(n => n.kind === "ColonToken");
        if (colonIndex !== undefined && colonIndex !== -1) {
          const typeNode = node.children?.[colonIndex + 1];
          if (typeNode && typeNode.varId) {
            allConstraints.push(["annotation", paramIdNode.varId!, typeNode.varId, `annotation ${paramIdNode.text!} : ${typeNode.text!}`]);
            // return 
          }
        }
        
        // 处理初始化
        const equalIndex = node.children?.findIndex(n => n.kind === "FirstAssignment");
        if (equalIndex !== undefined && equalIndex !== -1) {
          const right = node.children?.[equalIndex + 1];
          if (right && right.varId) {
            allConstraints.push(["sameType", paramIdNode.varId!, right.varId, `parameter ${paramIdNode.text!} = ${right.text!}`]);
            // return 
          }
        }

        let funcIdNode = node.parent;
        while (funcIdNode && funcIdNode.kind !== "FunctionDeclaration" && funcIdNode.kind !== "MethodDeclaration" && funcIdNode.kind !== "ArrowFunction" && funcIdNode.kind !== "Constructor" && funcIdNode.kind !== "FunctionExpression") funcIdNode = funcIdNode.parent;
        funcIdNode = funcIdNode?.kind === "ArrowFunction" || funcIdNode?.kind === "FunctionExpression" ? funcIdNode : funcIdNode?.children?.find(n => n.kind === "Identifier" || n.kind === "ConstructorKeyword");
        if (!funcIdNode || !funcIdNode.varId) return;

        allConstraints.push(["setParamType", funcIdNode.varId!, paramIdNode.varId!, `parameter ${paramIdNode.text!} in function ${funcIdNode.text!}`]);
        if (!funcParam[funcIdNode.varId]) funcParam[funcIdNode.varId] = [];
        funcParam[funcIdNode.varId].push(paramIdNode.varId);
      }
    },
    // 处理枚举声明
    EnumDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId !== undefined) {
          const typeId = newTypeNode({ kind: "enum", name: idNode.text!, members: {} });
          setTypeVar(idNode.varId!, typeId);
          varBindings.set(idNode.text!, idNode.varId!);
        }

        //处理namespace
        let paNode = node.parent?.parent?.parent;
        if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
        paNode = paNode.children?.find(n => n.kind === "Identifier");
        if (!paNode) return;
        allConstraints.push(["initProperty", paNode.varId!, idNode.varId!, `${paNode.text!}.${idNode.text!}`]);
        allConstraints.push(["takeProperty", idNode.varId!, paNode.varId!, `${idNode.text!}.${paNode.text!}`]);
      }
    },
    // 处理枚举成员
    EnumMember(node) {
      const idNode = node.children?.find(n => n.kind === "Identifier");
      const paNode = findParentByKind(node, "EnumDeclaration")?.children?.find(n => n.kind === "Identifier");
      const nb = node.children?.find(n => n.kind === "FirstLiteralToken");
      if(!paNode || !paNode.varId || !idNode || !idNode || !nb?.text) return;
      varBindings.set(idNode.text!, idNode.varId!);

      const oldTypeId = typeSet.get(paNode.varId!);
      if (!oldTypeId) return;
      const oldTypeNode = typeNodes.get(oldTypeId);
      if (!oldTypeNode || oldTypeNode.kind !== "enum") return;
      const newMembers = { ...oldTypeNode.members };
      newMembers[idNode.text!] = newTypeNode({ kind: "primitive", name: nb.text});

      const typeId = newTypeNode({ kind: "enum", name: idNode.text!, members: newMembers });
      setTypeVar(paNode.varId!, typeId);
    },
    // 处理接口声明
    InterfaceDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId !== undefined) {
          const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
          setTypeVar(idNode.varId!, typeId);
          varBindings.set(idNode.text!, idNode.varId!);
        }

        //处理namespace
        let paNode = node.parent?.parent?.parent;
        if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
        paNode = paNode.children?.find(n => n.kind === "Identifier");
        if (!paNode) return;
        allConstraints.push(["initProperty", paNode.varId!, idNode.varId!, `${paNode.text!}.${idNode.text!}`]);
        allConstraints.push(["takeProperty", idNode.varId!, paNode.varId!, `${idNode.text!}.${paNode.text!}`]);
      }
    },
    // 处理接口property
    PropertySignature(node) {
      if (node.children && node.children.length >= 2) {
        let idNode = node.parent;
        while (idNode && idNode.kind !== "InterfaceDeclaration") idNode = idNode.parent;
        idNode = idNode?.children?.find(n => n.kind === "Identifier");
        if (!idNode || idNode.varId === undefined) return;

        const propIdNode = node.children?.find(n => n.kind === "Identifier");
        if (!propIdNode || propIdNode.varId === undefined || !propIdNode.text) return;

        varBindings.set(propIdNode.text, propIdNode.varId!);

        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 处理类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            allConstraints.push(["initProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
            allConstraints.push(["takeProperty", propIdNode.varId!, idNode.varId!, `${propIdNode.text!}.${idNode.text!}`]);
            allConstraints.push(["annotation", propIdNode.varId, typeNode.varId, `annotation ${idNode.text!}.${propIdNode.text!} : ${typeNode.text!}`]);
          }
        } else {
          allConstraints.push(["initProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
          allConstraints.push(["takeProperty", propIdNode.varId!, idNode.varId!, `${propIdNode.text!}.${idNode.text!}`]);
        }
      }
    },
    // 处理Interface方法声明
    MethodSignature(node) {
      if (node.children && node.children.length >= 2) {
        let idNode = node.parent;
        while (idNode && idNode.kind !== "InterfaceDeclaration") idNode = idNode.parent;
        idNode = idNode?.children?.find(n => n.kind === "Identifier");
        if (!idNode || idNode.varId === undefined) return;

        const methodIdNode = node.children?.find(n => n.kind === "Identifier");
        if (!methodIdNode || methodIdNode.varId === undefined || !methodIdNode.text) return;

        varBindings.set(methodIdNode.text, methodIdNode.varId!);

        let funcType: TypeNode = { kind: "function", name: methodIdNode?.text!, id: methodIdNode?.varId!, params: [], returnType: UNKNOWN };
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            allConstraints.push(["returnAnnotation", methodIdNode.varId, typeNode.varId, `return type of method ${idNode.text!}`]);
          }
        } else {
          funcType.returnType = UNKNOWN;
        }

        const typeId = newTypeNode(funcType);
        setTypeVar(methodIdNode.varId!, typeId);

        allConstraints.push(["initProperty", idNode.varId, methodIdNode.varId, `${idNode.text}.${methodIdNode.text!}`]);
        // allConstraints.push(["takeProperty", methodIdNode.varId!, idNode.varId!, `${methodIdNode.text!}.${idNode.text!}`]);
      }
    },
    // 处理class声明
    ClassDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId) {
          const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
          if (LOG_IDENTIFIER_NODE)
            console.log(`Class ${idNode.text} has type ID ${typeId}`);
          setTypeVar(idNode.varId!, typeId);
          varBindings.set(idNode.text!, idNode.varId!);

          // 添加this指向
          if (node.children?.some(n => n.kind === "FirstPunctuation")) {
            paramBindings.set("this", idNode.varId!);
          }
        }
      }
    },
    // 处理classProperty
    PropertyDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        let idNode = node.parent;
        while (idNode && idNode.kind !== "ClassDeclaration") idNode = idNode.parent;
        idNode = idNode?.children?.find(n => n.kind === "Identifier");
        if (!idNode || idNode.varId === undefined) return;

        const propIdNode = findNodesByKind(node, "Identifier")[0];
        if (!propIdNode || propIdNode.varId === undefined) return;

        allConstraints.push(["initProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
        allConstraints.push(["takeProperty", propIdNode.varId!, idNode.varId!, `${propIdNode.text!}.${idNode.text!}`]);
        

        const colonNode = node.children.find(n => n.kind === "ColonToken");
        const equalNode = node.children.find(n => n.kind === "FirstAssignment");


        // 处理类型注解
        if (colonNode && colonNode.varId) {
          const index = node.children?.findIndex(n => n.kind === "ColonToken");
          if (index !== undefined && index !== -1) {
            const typeNode = colonNode!.parent!.children?.[index + 1];
            if (typeNode && typeNode.varId) {
              allConstraints.push(["annotation", propIdNode.varId, typeNode.varId, `annotation ${idNode.text!}.${propIdNode.text!} : ${typeNode.text!}`]);
            }
          }
        }

        // 处理初始化
        if (equalNode && equalNode.varId) {
          const index = node.children?.findIndex(n => n.kind === "FirstAssignment");
          if (index !== undefined && index !== -1) {
            const right = node.children?.[index + 1];
            if (right && right.varId) {
              allConstraints.push(["sameType", propIdNode.varId, right.varId, `${idNode.text!}.${propIdNode.text!} = ${right.text!}`]);
            }
          }
        }
      }
    },
    // 处理类方法
    MethodDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        let idNode = node.parent;
        while (idNode && idNode.kind !== "ClassDeclaration" && idNode.kind !== "ObjectLiteralExpression") idNode = idNode.parent;
        idNode = idNode?.kind === "ObjectLiteralExpression" ? idNode : idNode?.children?.find(n => n.kind === "Identifier");
        if (!idNode || idNode.varId === undefined) return;

        const propIdNode = node.children?.find(n => n.kind === "Identifier");
        if (propIdNode && propIdNode.varId !== undefined) {

          let funcType: TypeNode = { kind: "function", name: propIdNode?.text!, id: propIdNode?.varId!, params: [], returnType: UNKNOWN };
          const index = node.children?.findIndex(n => n.kind === "ColonToken");
          // 类型注解
          if (index !== undefined && index !== -1) {
            const typeNode = node.children?.[index + 1];
            if (typeNode && typeNode.varId) {
              allConstraints.push(["returnAnnotation", propIdNode.varId, typeNode.varId, `return type of method ${idNode.text!}`]);
            }
          } else if (findNodesByKind(node, "ReturnStatement").length === 0) {
            // 如果没有返回类型注解并且没有Return语句
            funcType.returnType = VOID;
          } else {
            funcType.returnType = UNKNOWN;
          }

          const typeId = newTypeNode(funcType);
          setTypeVar(propIdNode.varId!, typeId);

          allConstraints.push(["initProperty", idNode.varId, propIdNode.varId, `${idNode.text}.${propIdNode.text!}`]);
          // allConstraints.push(["takeProperty", propIdNode.varId!, idNode.varId!, `${propIdNode.text!}.${idNode.text!}`]);
        }
      }
    },
    Constructor(node) {
      if (node.children && node.children.length >= 2) {
        let idNode = node.parent;
        while (idNode && idNode.kind !== "ClassDeclaration" && idNode.kind !== "ObjectLiteralExpression") idNode = idNode.parent;
        idNode = idNode?.kind === "ObjectLiteralExpression" ? idNode : idNode?.children?.find(n => n.kind === "Identifier");
        if (!idNode || idNode.varId === undefined) return;

        const propIdNode = node.children?.find(n => n.kind === "ConstructorKeyword");
        if (propIdNode && propIdNode.varId !== undefined) {
          constructors[idNode.varId] = propIdNode?.varId;
          let funcType: TypeNode = { kind: "function", name: propIdNode?.text!, id: propIdNode?.varId!, params: [], returnType: VOID };
          const typeId = newTypeNode(funcType);
          setTypeVar(propIdNode.varId!, typeId);

          allConstraints.push(["initProperty", idNode.varId, propIdNode.varId, `${idNode.text}.${propIdNode.text!}`]);
        }
      }
    },
    // 处理模块声明
    ModuleDeclaration(node) {
      const idNode = node.children?.find(n => n.kind === "Identifier");

      if(idNode && idNode.varId) {
        const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
        setTypeVar(idNode.varId!, typeId);
        varBindings.set(idNode.text!, idNode.varId!);
      }
    },
    // 处理import声明
    ImportDeclaration(node) {
      const raw = node.children?.find(n => n.kind === "StringLiteral")?.text;
      const moduleSpecifier = raw?.replace(/^['"]|['"]$/g, "");  // 去掉引号
      if (!moduleSpecifier) {
        if (LOG_IMPORT)
          console.warn(`ImportDeclaration in ${filePath} has no moduleSpecifier`);
        return;
      }

      const resolvedFile = resolveImportPath(filePath, moduleSpecifier);
      if (!resolvedFile) {
        if (LOG_IMPORT)
          console.warn(`can not resolve import ${moduleSpecifier} in ${filePath}`);
      }

      let idNode;

      // import * as x from "xxx"
      const nsimpt = findNodesByKind(node, "NamespaceImport")[0];
      idNode = nsimpt?.children?.find(n => n.kind === "Identifier");
      if (idNode?.varId && idNode?.text) {
        const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
        setTypeVar(idNode.varId!, typeId);
        varBindings.set(idNode.text, idNode.varId);

        if (!resolvedFile) {
          allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
        } else {
          for (const symb in globalExportMap[resolvedFile]) {
            allConstraints.push(["initProperty", idNode.varId!, globalExportMap[resolvedFile]?.[symb], `${idNode.text!}.${symb}`]);
            allConstraints.push(["takeProperty", globalExportMap[resolvedFile]?.[symb], idNode.varId!, ``]);
          }
        }
      }

      // import {A as a, B} from "xxx"
      const ndimpts = findNodesByKind(node, "ImportSpecifier");
      for (const ndimpt of ndimpts) {
        let target;
        if (ndimpt.children?.length === 1) {
          idNode = ndimpt.children[0];
          varBindings.set(idNode.text!, idNode.varId!);

          if (!resolvedFile) {
            allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
          } else {
            target = globalExportMap[resolvedFile]?.[idNode.text!];
          }
        } else if(ndimpt.children?.length === 3) {
          idNode = ndimpt.children[2];
          varBindings.set(idNode.text!, idNode.varId!);

          if (!resolvedFile) {
            allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
          } else {
            target = globalExportMap[resolvedFile]?.[ndimpt.children[0].text!];
          }
        }

        if (target !== undefined && idNode) {
          allConstraints.push(["sameType", idNode.varId!, target, `Success import ${idNode.text} from ${moduleSpecifier}`]);
        }
      }

      // import x from "xxx"
      const impt = findNodesByKind(node, "ImportClause")[0];
      for (const idNode of impt?.children?.filter(c => c.kind === "Identifier") || []) {
        varBindings.set(idNode.text!, idNode.varId!);

        if (!resolvedFile) {
          allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
        } else {
          const target = globalExportMap[resolvedFile]?.[idNode.text!] === undefined? globalExportMap[resolvedFile]?.["default"] : globalExportMap[resolvedFile]?.[idNode.text!];
          if (target !== undefined) {
            allConstraints.push(["sameType", idNode.varId!, target, `Success import ${idNode.text} from ${moduleSpecifier}`]);
          }
        }
      }
    },
    // 处理export xxx from xxx
    ExportDeclaration(node) {
      const raw = node.children?.find(n => n.kind === "StringLiteral")?.text;
      const moduleSpecifier = raw?.replace(/^['"]|['"]$/, ""); // 去掉引号
      if (!moduleSpecifier) {
        if (LOG_IMPORT)
          console.warn(`ImportDeclaration in ${filePath} has no moduleSpecifier`);
        return;
      }
      const resolvedFile = resolveImportPath(filePath, moduleSpecifier);
      
      const ndepts = node?.children?.find(c => c.kind === "NamedExports");
      if (ndepts) {
        const expts = findNodesByKind(ndepts, "ExportSpecifier");
        for (const expt of expts)
          if (expt.children && expt.children.length > 0 && expt.children[0].kind === "Identifier" && expt.children[0].text) {
            const idNode = expt.children[0];
            const symbol = idNode.text!;
            varBindings.set(symbol, idNode.varId!);
            if (!resolvedFile) {
              if (LOG_IMPORT)
                console.warn(`can not resolve import ${moduleSpecifier} in ${filePath}`);
              allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
              continue;
            }

            const target = globalExportMap[resolvedFile]?.[symbol] === undefined? globalExportMap[resolvedFile]?.["default"] : globalExportMap[resolvedFile]?.[symbol];
            if (target !== undefined) {
              allConstraints.push(["sameType", idNode.varId!, target, `Success import ${symbol} from ${moduleSpecifier}`]);
            } else {
              // export xxx from file
              function findfa(file: string) : number | undefined {
                for (let dst of globalExportFa[file]?.[symbol] || []) {
                  console.log(`now in ${dst} finding ${symbol} at ${file}`);
                  if (globalExportMap[dst]?.[symbol]) {
                    globalExportMap[file] ??= {};
                    globalExportMap[file][symbol] = globalExportMap[dst][symbol];
                    return globalExportMap[dst][symbol];
                  }
                  else return findfa(dst);
                }
                for (let dst of globalExportFa[file]?.["*"] || []) {
                  console.log(`now in ${dst} finding ${symbol} at ${file}`);
                  if (globalExportMap[dst]?.[symbol]) {
                    globalExportMap[file] ??= {};
                    globalExportMap[file][symbol] = globalExportMap[dst][symbol];
                    return globalExportMap[dst][symbol];
                  }
                  const res = findfa(dst);
                  if (res) return res;
                }
                return undefined;
              }
              const ret = findfa(resolvedFile);
              if (ret) {
                allConstraints.push(["sameType", idNode.varId!, ret, `Asesome! Success import ${symbol}(*) from ${moduleSpecifier}`]);
              } else {
                if (LOG_IMPORT)
                  console.warn(`Symbol ${symbol} not found in export map of ${resolvedFile} in ${filePath}`);
                allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
              }
            }
          }
      }
    }
  }

  const handlers: Record<string, (node: AstNode) => void> = {
    StringLiteral(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
      syntaxNodes[node.varId!].v8kind = "Literal"
    },
    NoSubstitutionTemplateLiteral(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
    },
    FirstLiteralToken(node) {
      // 暂时默认为数字
      allConstraints.push(["hasType", node.varId!, NUMBER, `${node.text!} ∈ number`]);
      syntaxNodes[node.varId!].v8kind = "Literal"
    },
    NumericLiteral(node) {
      allConstraints.push(["hasType", node.varId!, NUMBER, `${node.text!} ∈ number`]);
      syntaxNodes[node.varId!].v8kind = "Literal"
    },
    TrueKeyword(node) {
      allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
      syntaxNodes[node.varId!].v8kind = "Literal"
    },
    FalseKeyword(node) {
      allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
      syntaxNodes[node.varId!].v8kind = "Literal"
    },
    NullKeyword(node) {
      allConstraints.push(["hasType", node.varId!, NULL, `${node.text!} ∈ null`]);
      syntaxNodes[node.varId!].v8kind = "Literal"
    },
    BigIntLiteral(node) {
      allConstraints.push(["hasType", node.varId!, NUMBER, `${node.text!} ∈ number`]);
      syntaxNodes[node.varId!].v8kind = "Literal"
    },
    RegularExpressionLiteral(node) {
      allConstraints.push(["hasType", node.varId!, REGEXP, `${node.text!} ∈ RegExp`]);
      syntaxNodes[node.varId!].v8kind = "RegExpLiteral"
    },
    ArrayLiteralExpression(node) {
      syntaxNodes[node.varId!].v8kind = "ArrayLiteral"
      for (const child of node.children?.find(c => c.kind === "SyntaxList")?.children?.filter(c => c.kind !== "CommaToken") || []) {
        allConstraints.push(["makeArray", node.varId!, child.varId!, `element ${child.text!} of array ${node.text!}`]);
        setTypeVar(node.varId!, newTypeNode({ kind: "array", elementType: UNKNOWN }));
      }
    },
    TemplateExpression(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
      syntaxNodes[node.varId!].v8kind = "TemplateLiteral";
    },
    FirstTemplateToken(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
      syntaxNodes[node.varId!].v8kind = "TemplateLiteral";
    },
    // 处理类型关键字
    NumberKeyword(node) {
      if (node.varId === undefined) return;
      allConstraints.push(["hasType", node.varId, NUMBER, `${node.text!} ∈ number`]);
    },
    StringKeyword(node) {
      if (node.varId === undefined) return;
      allConstraints.push(["hasType", node.varId, STRING, `${node.text!} ∈ string`]);
    },
    BooleanKeyword(node) {
      if (node.varId === undefined) return;
      allConstraints.push(["hasType", node.varId, BOOLEAN, `${node.text!} ∈ boolean`]);
    },
    VoidKeyword(node) {
      if (node.varId === undefined) return;
      allConstraints.push(["hasType", node.varId, VOID, `${node.text!} ∈ void`]);
    },
    AnyKeyword(node) {
      if (node.varId === undefined) return;
      allConstraints.push(["hasType", node.varId, ANY, `${node.text!} ∈ any`]);
    },
    UndefinedKeyword(node) {
      if (node.varId === undefined) return;
      allConstraints.push(["hasType", node.varId, UNDEFINED, `${node.text!} ∈ undefined`]);
    },
    ObjectKeyword(node) {
      // 用法存疑
      if (node.varId === undefined) return;
      const id = newTypeNode({ kind: "object", name: "Object", id: node.varId!, properties: Object.create(null) });
      allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ Object`]);
    },
    ThisKeyword(node) {
      if (node.varId === undefined) return;
      // syntaxNodes[node.varId!].v8kind = "ThisExpression";

      // this关键字通常在类方法中使用
      // let classNode = node.parent;
      // while(classNode && classNode.kind !== "ClassDeclaration") classNode = classNode.parent;
      // if (classNode && classNode.varId !== undefined) {
      //   // 在类中this指向当前类实例
      //   const idNode = classNode.children?.find(n => n.kind === "Identifier");
      //   if (idNode && idNode.varId !== undefined) {
      //     allConstraints.push(["sameType", node.varId, idNode.varId, `this in class ${idNode.text!}`]);
      //     return;
      //   }
      // }
      const typeId = varBindings.get("this");

      if (typeId !== undefined) {
        allConstraints.push(["sameID", node.varId!, typeId, `same identifier: ${node.text!}`]);
      }
      else {
        // varBindings.set(node.text, node.varId!);
        // console.warn(`Identifier ${node.text} not found in varBindings, using its own varId ${node.varId}`);
      }
    },
    LiteralType(node) {
      if (node.varId === undefined) return;
      const id = newTypeNode({ kind: "primitive", name: node.text || "unknown LiteralType" });
      allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ ${node.text!}`]);
    },
    ArrayType(node) {
      if (node.children && node.children.length >= 3) {
        const elementTypeNode = node.children[0];
        if (elementTypeNode.varId !== undefined && node.varId !== undefined) {
          allConstraints.push(["makeArray", node.varId, elementTypeNode.varId, `${node.text!} ∈ ${elementTypeNode.text}[]`]);
          setTypeVar(node.varId!, newTypeNode({ kind: "array", elementType: UNKNOWN }) );
        }
      }
    },
    UnionType(node) {
      // UnionTypee : { SyntaxList : { keywd1 | keywd2 } } 
      if (node.children) {
        const n = node.children[0];
        if (n.children && n.children.length > 0) {
          const types: number[] = [];
          for (const child of n.children) {
            if (child.varId !== undefined && child.kind !== "BarToken") {
              allConstraints.push(["sameType", node.varId!, child.varId, `UnionType ${child.text!}`]);
            }
          }
        }
      }
    },
    PropType(node) {
      // if (node.children) {
      //   const types: number[] = [];
      //   for (const child of node.children[0].children || []) {
      //     if (child.varId !== undefined && child.varId in typeNodes) {
      //       types.push(child.varId);
      //     }
      //   }
      //   if (types.length > 0 && node.varId !== undefined) {
      //     const id = newTypeNode({ kind: "union", types });
      //     allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ ${types.map(printType).join(" | ")}`]);
      //   }
      // }
    },
    FunctionType(node) {
      // (param1: type1, param2: type2) => returnType
      // 清空param参数
      paramBindings.clear();
      // TODO
    },
    TypeReference(node) {
      // TODO
      if (node.children) {
        // const idNode = node.children[0];
        // if (idNode.varId !== undefined && idNode.text) {
        //   const typeId = varBindings.get(idNode.text);
        //   if (typeId !== undefined) {
        //     allConstraints.push(["sameID", node.varId!, typeId, `same Type: ${idNode.text!}`]);
        //   } else {
        //     // console.warn(`TypeReference ${idNode.text} not found in varBindings`);
        //   }
        // }
        const idNode = node.children[0];
        if (idNode.varId !== undefined) {
          allConstraints.push(["sameID", node.varId!, idNode.varId, `TypeReference ${idNode.text!}`]);
        }
      }
    },
    FirstNode(node) {
      // 处理类型 例：window.WindowStage
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        // 处理点运算符
        if (operator.kind === "DotToken" && left.varId !== undefined && right.varId !== undefined) {
          // 处理属性访问
          const propName = right.text;
          if (propName) {
            allConstraints.push(["takeProperty", node.varId!, left.varId!, `${left.text!}.${propName}`]);
          }
        }
      }
    },
    TypeOfExpression(node) {
      syntaxNodes[node.varId!].v8kind = "UnaryOperation";
    },
    VoidExpression(node) {
      syntaxNodes[node.varId!].v8kind = "UnaryOperation";
    },
    YieldExpression(node) {
      syntaxNodes[node.varId!].v8kind = node.children?.find(c => c.kind === "AsterisToken") ? "YieldStar" : "Yield";
    },
    // 处理一元操作
    PrefixUnaryExpression(node) {
      if (node.children && node.children.length >= 2) {
        const operator = node.children[0];
        const exprNode = node.children[1];
        syntaxNodes[node.varId!].offset = operator.offset;
        syntaxNodes[node.varId!].v8kind = operator.text === "++" || operator.text === "--" ? "CountOperation" : "UnaryOperation";
        if (exprNode.varId !== undefined) {
          if (operator.kind === "ExclamationToken") {
            allConstraints.push(["hasType", node.varId!, BOOLEAN, `!${exprNode.text!} ∈ boolean`]);
            allConstraints.push(["refersTo", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
          } else if (operator.kind === "MinusToken") {
            allConstraints.push(["sameType", node.varId!, exprNode.varId!, `-${exprNode.text!}`]);
            allConstraints.push(["refersTo", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
          }
        }
      }
      // TODO: 处理其他一元操作
    },
    PostfixUnaryExpression(node) {
      syntaxNodes[node.varId!].v8kind = "CountOperation";
    },
    // 二元操作
    BinaryExpression(node) {
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        syntaxNodes[node.varId!].offset = operator.offset;
        // 处理赋值操作
        if (left.varId !== undefined && right.varId !== undefined && (operator.kind === "FirstAssignment" || operator.kind === "FirstCompoundAssignment" || operator.kind === "MinusEqualsToken" || operator.kind === "AsteriskEqualsToken" || operator.kind === "SlashEqualsToken" || operator.kind === "PercentEqualsToken" || operator.kind === "AsteriskAsteriskEqualsToken" || operator.kind === "AmpersandEqualsToken" || operator.kind === "BarEqualsToken")) {
          syntaxNodes[node.varId!].v8kind = operator.kind === "FirstAssignment" ? "Assignment" : "CompoundAssignment";
          syntaxNodes[left.varId!].v8kind = undefined;
          allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
          allConstraints.push(["sameType", node.varId!, right.varId, `${node.text!} = ${right.text!}`]);
          // allConstraints.push(["sameType", right.varId!, left.varId, `${left.text!} = ${right.text!}`]);
          // 处理对象属性设置
          if (left.kind === "PropertyAccessExpression" && left.children && left.children.length! >= 3) {
            syntaxNodes[node.varId!].v8kind = undefined;
            allConstraints.push(["setProperty", left.children[0].varId!, left.varId, `${left.children[0].text}.${left.children[2].text} = ${right.text}`]);
          } else if (left.kind === "ElementAccessExpression" && left.children && left.children.length! >= 4) {
            syntaxNodes[node.varId!].v8kind = undefined;
            allConstraints.push(["setElement", left.children[0].varId!, left.varId, `${left.children[0].text}[${left.children[2].text}] = ${right.text}`]);
          }
        }
        // 处理加减乘除模运算
        else if (left.varId !== undefined && right.varId !== undefined && (operator.kind === "PlusToken" || operator.kind === "MinusToken" || operator.kind === "AsteriskToken" || operator.kind === "SlashToken" || operator.kind === "PercentToken" || operator.kind === "AsteriskAsteriskToken")) {
          // allConstraints.push(["sameType", left.varId!, right.varId!, `${left.text!} == ${right.text!}`]);
          syntaxNodes[node.varId!].v8kind = "BinaryOperation";
          allConstraints.push(["sameType", node.varId!, right.varId!, `${node.text!} = ${right.text!}`]);
          allConstraints.push(["sameType", node.varId!, left.varId!, `${node.text!} == ${left.text!}`]);
        }
        // 处理逻辑运算
        else if (left.varId !== undefined && right.varId !== undefined && (operator.kind === "AmpersandAmpersandToken" || operator.kind === "BarBarToken")) {
          syntaxNodes[node.varId!].v8kind = "BinaryOperation";
          allConstraints.push(["sameType", node.varId!, left.varId!, `${node.text!} = ${left.text!}`]);
          allConstraints.push(["sameType", node.varId!, right.varId!, `${node.text!} = ${right.text!}`]);
        }
        // 处理比较运算
        else if (left.varId !== undefined && right.varId !== undefined && (operator.kind === "LessThanToken" || operator.kind === "GreaterThanToken" || operator.kind === "LessThanEqualsToken" || operator.kind === "GreaterThanEqualsToken" || operator.kind === "EqualsEqualsToken" || operator.kind === "ExclamationEqualsToken" || operator.kind === "EqualsEqualsEqualsToken" || operator.kind === "ExclamationEqualsEqualsToken")) {
          allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
          syntaxNodes[node.varId!].v8kind = "CompareOperation";
          // 认为是同一类型
          // allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} ${operator.text} ${right.text}`]);
          // allConstraints.push(["sameType", right.varId, left.varId, `${left.text!} ${operator.text} ${right.text}`]);
        }
        // TODO: 更多二元运算
      }
    },
    // 处理数组字面量
    ElementAccessExpression(node) {
      syntaxNodes[node.varId!].v8kind = "Property"
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const right = node.children[2];
        syntaxNodes[node.varId!].offset = node.children[1].offset;
        if (left.varId !== undefined && node.varId !== undefined) {
          allConstraints.push(["elementAccess", node.varId, left.varId, `${left.text!}[${right.text!}]`]);
        }
      }
    },
    // 处理属性访问
    PropertyAccessExpression(node) {
      syntaxNodes[node.varId!].v8kind = "Property"
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        syntaxNodes[node.varId!].offset = right.offset;
        syntaxNodes[right.varId!].v8kind = undefined;
        // 处理dot运算符
        if ((operator.kind === "DotToken" || operator.kind === "QuestionDotToken") && left.varId !== undefined && right.varId !== undefined) {
          // 处理属性访问
          const propName = right.text;
          if (propName) {
            allConstraints.push(["takeProperty", node.varId!, left.varId!, `${left.text!}.${propName}`]);
          }
        }
      }
    },
    PropertyAssignment(node) {
      if (node.children) {
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        if (index !== undefined && index !== -1) {
          const right = node.children?.[index + 1];
          if (right && right.varId) {
            // syntaxNodes[right.varId].v8kind = undefined;
          }
        }
      }
    },
    // New运算符
    NewExpression(node) {
      syntaxNodes[node.varId!].v8kind = "CallNew"
      if (node.children) {
        const classNode = node.children.find(n => n.kind === "Identifier");
        if (classNode?.varId !== undefined) {
          allConstraints.push(["sameType", node.varId!, classNode.varId, `new ${classNode.text!}`]);

          // 处理实参
          const cls = varBindings.get(classNode.text!);
          if (!cls) {
            console.warn(`Can not find correspond class for new expression ${node.text}`)
            return;
          }
          const constr = constructors[cls];
          if (constr) {
            const args = node.children.find(n => n.kind === "SyntaxList");
            let idx = 0;
            for (const arg of args?.children?.filter(n => n.kind !== "CommaToken") ?? []) {
              allConstraints.push(["funcToArg", arg.varId!, constr * 1000 + idx, `${node.text}`]);
              idx++;
            }
          }
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
      if (tsMorphNodes.includes(node.parent?.kind!)) syntaxNodes[node.varId!].v8kind = "VariableProxy";
      if (node.text) {
        if (node.text === "undefined") {
          allConstraints.push(["hasType", node.varId!, UNDEFINED, `${node.text!} ∈ undefined`]);
          return;
        }
        let typeId = paramBindings.get(node.text);

        if (typeId !== undefined) {
          allConstraints.push(["sameID", node.varId!, typeId, `same identifier: ${node.text!}`]);
        }
        else {
          typeId = varBindings.get(node.text);
          if (typeId !== undefined) {
            allConstraints.push(["sameID", node.varId!, typeId, `same identifier: ${node.text!}`]);
          }
        }
      }
    },
    // 处理for...of循环
    ForOfStatement(node) {
      // TODO:
      // if (node.children && node.children.length >= 4) {
      //   const srcNode = node.children?.filter(n => n.kind === "Identifier")[0];
      //   const dstNode = findNodesByKind(node, "Identifier")[0];
      //   if (srcNode && dstNode && srcNode.varId !== undefined && dstNode.varId !== undefined) {
      //     allConstraints.push(["xxx", dstNode.varId, srcNode.varId, `for...of ${srcNode.text!} in ${dstNode.text!}`]);
      //   }
      // }
    },
    // 处理三元表达式
    ConditionalExpression(node) {
      syntaxNodes[node.varId!].v8kind = "Conditional";
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
    // 处理返回值
    ReturnStatement(node) {
      // syntaxNodes[node.varId!].v8kind = "ReturnStatement";
      if (node.children && node.children.length >= 2) {
        const exprNode = node.children[1];

        let funcNode = node.parent;
        while (funcNode && funcNode.kind !== "FunctionDeclaration" && funcNode.kind !== "MethodDeclaration" && funcNode.kind !== "ArrowFunction" && funcNode.kind !== "FunctionExpression") funcNode = funcNode.parent;
        funcNode = funcNode?.kind === "ArrowFunction" || funcNode?.kind === "FunctionExpression" ? funcNode : funcNode?.children?.find(n => n.kind === "Identifier");

        if (!funcNode || !funcNode.varId || !exprNode.varId) return;
        if (exprNode.kind === "SemicolonToken") {
          allConstraints.push(["hasType", node.varId!, VOID, "return; ∈ VOID"]);
          allConstraints.push(["returnType", node.varId!, node.varId!, `return;`]);
        }
        else
          allConstraints.push(["returnType", funcNode.varId!, exprNode.varId!, `return value of function ${funcNode.text!}`]);
      }
    },
    // 处理函数调用
    CallExpression(node) {
      syntaxNodes[node.varId!].v8kind = "Call";
      if (node.children && node.children.length >= 2) {
        // 不能改为在bindings中查找，因为有可能是匿名函数调用
        const funcNode = node.children[0];
        if (funcNode.varId !== undefined && node.varId !== undefined) {
          syntaxNodes[node.varId!].offset = funcNode.kind === "PropertyAccessExpression" ? funcNode.children?.[2]?.offset : funcNode.offset;
          allConstraints.push(["funcCall", node.varId, funcNode.varId, `${node.text}`]);

          // 处理实参
          const args = node.children.find(n => n.kind === "SyntaxList");
          let idx = 0;
          for (const arg of args?.children?.filter(n => n.kind !== "CommaToken") ?? []) {
            allConstraints.push(["funcToArg", arg.varId!, funcNode.varId * 1000 + idx, `${node.text}`]);
            idx++;
          }
        }
      }
    },
    // 处理箭头函数 () => {}
    ArrowFunction(node) {
      // 如果没有block，退出作用域，必须postOrder!
      syntaxNodes[node.varId!].v8kind = "FunctionLiteral";
      if (!node.children?.some(n => n.kind === "Block")) {
        const previous = scopeStack.pop();
        if (previous) {
          if (LOG_SCOPE) {
            console.log(`Exiting scope for ArrowFunction at line ${node.position?.start?.line}, column ${node.position?.start?.character} in ${filePath}`);
            for (const [name, id] of varBindings.entries()) {
              if (!previous.has(name) || previous.get(name) !== id) {
                console.log(`  ${name} -> ${id}`);
              }
            }
          }
          varBindings = previous;  // 恢复上层作用域
        } else {
          throw new Error("Scope stack underflow: too many closing braces");
        }
      }
      // TODO: 其余操作
      if (node.children) {
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: node.varId!, params: [], returnType: UNKNOWN });
            setTypeVar(node.varId!, id);
            allConstraints.push(["returnAnnotation", node?.varId!, typeNode.varId, `return type of function ${node?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: node?.varId!, params: [], returnType: VOID });
         setTypeVar(node.varId!, id);
        }
        else {
          const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: node?.varId!, params: [], returnType: UNKNOWN });
         setTypeVar(node.varId!, id);
        }
      }

    },
    // => 操作符
    EqualsGreaterThanToken(node) {
      // 如果没有block，手动创建作用域
      if (node && node.parent && node.parent.kind === "ArrowFunction" && !node.parent.children?.some(n => n.kind === "Block")) {
        if (LOG_SCOPE)
          console.log(`Creating scope for ArrowFunction at line ${node.position?.start?.line}, column ${node.position?.start?.character} in ${filePath}`);
        scopeStack.push(varBindings);
        varBindings = new Map(varBindings);
        // 加入parameter绑定
        for (const [name, id] of paramBindings.entries()) {
          varBindings.set(name, id);
        }
        // 清空paramBindings
        paramBindings.clear();
      }
    },
    // 处理类型断言
    AsExpression(node) {
      if (node.children && node.children.length >= 3) {
        const exprNode = node.children[0];
        const typeNode = node.children[2];
        if (exprNode.varId !== undefined && node.varId !== undefined && typeNode.text) {
          allConstraints.push(["sameType", node.varId!, exprNode.varId!, `${exprNode.text!} as ${typeNode.text!}`]);
          // TODO: 添加类型断言约束
        }
      }
    },
    // 处理作用域{
    FirstPunctuation(node) {
      scopeStack.push(varBindings);
      varBindings = new Map(varBindings);
      // 加入parameter绑定
      for (const [name, id] of paramBindings.entries()) {
        varBindings.set(name, id);
      }
      // 清空paramBindings
      paramBindings.clear();
      if (LOG_SCOPE)
        console.log(`Entering scope at line ${node.position?.start?.line}, column ${node.position?.start?.character} in ${filePath}`);
    },
    // 处理作用域}
    CloseBraceToken(node) {
      // 恢复旧的变量绑定
      const previous = scopeStack.pop();
      if (previous) {
        if (LOG_SCOPE) {
          console.log(`Exiting scope at line ${node.position?.start?.line}, column ${node.position?.start?.character} in ${filePath}:`);
          for (const [name, id] of varBindings.entries()) {
            if (!previous.has(name) || previous.get(name) !== id) {
              console.log(`  ${name} -> ${id}`);
            }
          }
        }
        varBindings = previous;  // 恢复上层作用域
      } else {
        throw new Error("Scope stack underflow: too many closing braces");
      }
    }
  }



  function walk(node: AstNode) {
    const id = node.varId;
    if (id === undefined) throw new Error("Missing varId in second pass");
    syntaxNodes[id] = { kind: node.kind, text: node.text, file: filePath, position: node.position, offset: node.offset, context: node.parent?.text 
};
    // 处理先序遍历
    let handler = preOrderHandlers[node.kind];
    if (handler) handler(node);

    if (node.children) node.children.forEach(walk);

    // 处理后序遍历
    handler = handlers[node.kind];
    if (handler) handler(node);
  }

  walk(node);


  if (LOG_SCOPE)
    console.log(`Variable bindings in ${filePath}:`);
  for (const [name, id] of varBindings.entries()) {
    if (LOG_SCOPE)
      console.log(`${name} -> ${id}`);
    if (!globalVarBindings.has(name)) {
      globalVarBindings.set(name, id);
    } else {
      // 如果已经存在，合并类型
      // const existingId = globalVarBindings.get(name)!;
      // allConstraints.push(["sameType", existingId, id, `merge type for ${name}`]);
    }
  }
}

// 解析导入路径
function resolveImportPath(currentFilePath: string, importSpecifier: string): string | undefined {
  if (importSpecifier.startsWith(".")) {
    // 本地模块：相对路径 + 补后缀
    const realCurrentPath = path.basename(currentFilePath).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");
    const absbase = path.resolve(path.dirname(realCurrentPath), importSpecifier);
    const base = path.relative(process.cwd(), absbase);
    for (const extname of ["", ".ts", ".js", ".ets", ".tsx", ".d.ts", ".d.ets"]) {
      let ret = base + extname;
      if (fs.existsSync(path.join(path.dirname(currentFilePath), ret.replace(/\\/g, "^") + ".ast.json")))
        return ret;
      ret = base + "\\index" + extname;
      if (fs.existsSync(path.join(path.dirname(currentFilePath), ret.replace(/\\/g, "^") + ".ast.json")))
        return ret;
      // console.error(`base: ${path.join(path.dirname(currentFilePath), ret.replace(/\\/g, "^"))}`);
    }
    return undefined
  } else {
    // 外部模块 or 内建模块
    if (LOG_IMPORT)
      console.log(`Resolving external import: ${importSpecifier} in ${currentFilePath}`);
    // try {
    //   return require.resolve(importSpecifier, { paths: [path.dirname(currentFilePath)] });
    // } catch {
    //   return undefined;
    // }
    if (!importSpecifier.startsWith("@"))
      importSpecifier = importSpecifier.split("/")[0];
    if (globalImportMap.has(importSpecifier)) {
      // console.log(`${path.basename(globalImportMap.get(importSpecifier)!).replace(/\^/g, "\\").replace(/\.ast\.json/g, "")}`);
      return path.basename(globalImportMap.get(importSpecifier)!).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");
    }
  }
}

// 求解类型图
function deriveVariableTypes() {
  for (let [kind, a, b] of allConstraints) {
    a = find(Number(a));
    if (kind === "hasType") {
      if (syntaxNodes[a].kind === "Identifier") {
        graph.set(a, graph.get(a) ?? new Map());
      }
      setTypeVar(a, b); source.set(a, new Map());
    } else if (kind !== "sameID") {
      if (kind === "funcToArg") {
        const func = find(Math.floor(b / 1000));
        const idx = b % 1000;
        // if (!funcParam[func]?.[idx]) {
        //   console.log(`Can not find Correspond param #${idx} of function ${syntaxNodes[func]?.text!}[${func}]`);
        //   continue;
        // } else {
        //   console.log(`Find Correspond param #${idx} of function ${syntaxNodes[func]?.text!}[${func}]`);
        // }
        a = a * 1000 + idx;
        b = func;
      }
      b = find(Number(b));
      if (b === a) continue; // 避免自引用
      graph.set(b, graph.get(b) ?? new Map()); graph.get(b)!.set(a, kind);
      source.set(a, source.get(a) ?? new Map()); source.get(a)!.set(b, UNKNOWN);
      // if (kind === "setParamType" || kind === "initProperty") {
      //   setTypeVar(b, UNKNOWN);
      // }
    }
  }

  worklist = Array.from(graph.keys()).filter(n => typeSet.get(n) !== undefined);
  while (worklist.length > 0) {
    const cur = worklist.pop()!;
    cnt[cur] = (cnt[cur] ?? 0) + 1;
    if (cnt[cur] > 200) {
      console.warn(`Node ${cur} has too many iterations (${cnt[cur]}), possible infinite loop`);
      break;
    }
    console.log(`Processing node ${cur} (${syntaxNodes[cur]?.text}) with ${cnt[cur]} iterations, worklist size: ${worklist.length}, node edges ${graph.get(cur)?.size ?? 0}`);
    if (LOG_TYPE_FLOW) {
      console.log(`Processing node ${cur} (${syntaxNodes[cur]?.text}) with ${cnt[cur]} iterations:`);

      // 输出 Types
      if (typeSet.get(cur)) {
        console.log(`  Type (raw): ${typeSet.get(cur)}`);
        console.log(`  Type: ${JSON.stringify(typeNodes.get(typeSet.get(cur)!))}`);
      } else {
        console.log(`  Type: no types`);
      }
    }

    let tSet = typeSet.get(cur);
    if(!tSet) {
      console.warn(`node ${cur} with no type`);
      continue;
    }
    const edges = graph.get(cur);
    if (!edges) continue;
    for (const next of edges.keys()) {
      const nSet = typeSet.get(next);
      const edgeKind = graph.get(cur)!.get(next)!;
      console.log(`  Processing edge ${cur} -> ${next} of kind ${edgeKind}, merge difficulty: ${source.get(next)?.size ?? 0}`);


      //  数据流处理
      if (edgeKind === "sameType" || edgeKind === "ArgToParam" || edgeKind === "annotation") {
        if (edgeKind === "annotation" && syntaxNodes[cur].file && !path.relative(process.cwd(), syntaxNodes[cur].file).split(path.sep).includes("sdk")) continue;
        // 如果是同类型
        source.get(next)!.set(cur, tSet);
        setTypeVar(next, mergeBranches(next));
      }
      else if (edgeKind === "takeProperty") {
        // 如果是取属性，添加属性类型
        if (!syntaxNodes[next]?.text) {
          console.error(`fail to takeProperty because text size too short`);
          continue;
        } else {
          const propName = syntaxNodes[next]?.text.split(".").pop();
          const typeNode = typeNodes.get(tSet);
          if (propName && typeNode && typeNode.kind == "object" && propName in typeNode.properties) {
            source.get(next)?.set(cur, typeNode.properties[propName]);
            if (LOG_TYPE_FLOW)
              console.log(`takeProperty[object] ${typeNode.properties[propName]} for ${propName} in edge ${cur}->${next}`);
          } else if (propName && typeNode && typeNode.kind == "enum" && propName in typeNode.members) {
            source.get(next)?.set(cur, typeNode.members[propName]);
            if (LOG_TYPE_FLOW)
              console.log(`takeProperty[enum] ${typeNode.members[propName]} for ${propName} in edge ${cur}->${next}`);
          }
        }
        setTypeVar(next, mergeBranches(next) === UNKNOWN ? typeSet.get(next)! : mergeBranches(next));
      }
      else if (edgeKind === "elementAccess") {
        // 取数组成员
        const typeNode = typeNodes.get(tSet);
        if (typeNode?.kind === "array") {
          source.get(next)!.set(cur, mergeTypes([typeNode.elementType, UNDEFINED]));
        } else if (typeNode?.kind === "primitive" && typeNode.name === "string") {
          source.get(next)!.set(cur, mergeTypes([STRING, UNDEFINED]));
        } else if (typeNode?.kind === "object") {
          let propName = syntaxNodes[next]?.text?.split("[").pop()?.split("]")[0];
          // 只判断字符串或者数字属性
          if (propName && (propName.startsWith('"') && propName.endsWith('"') || propName.startsWith("'") && propName.endsWith("'") || /^\d+$/.test(propName))) {
            const cleanPropName = (propName.startsWith('"') && propName.endsWith('"') || propName.startsWith("'") && propName.endsWith("'")) ? propName.slice(1, -1) : propName;
            const propType = typeNode.properties[cleanPropName];
            if (propType) {
              source.get(next)!.set(cur, propType);
              if (LOG_TYPE_FLOW)
                console.log(`elementAccess[object] ${propType} for ${cleanPropName} in edge ${cur}->${next}`);
            }
          }
        }
        else if (typeNode?.kind === "union") {
          let lst = [];
          for (const subtype of typeNode.types) {
            const subtypeNode = typeNodes.get(subtype);
            if (subtypeNode?.kind === "array") {
              lst.push(subtypeNode.elementType);
              lst.push(UNDEFINED);
            } else if (subtypeNode?.kind === "primitive" && subtypeNode.name === "string") {
              lst.push(mergeTypes([STRING, UNDEFINED]));
            } else if (subtypeNode?.kind === "object") {
              const propName = syntaxNodes[cur]?.text?.split("[").pop()?.split("]")[0];
              if (propName && (propName.startsWith('"') && propName.endsWith('"') || propName.startsWith("'") && propName.endsWith("'"))) {
                const cleanPropName = propName.slice(1, -1);
                const propType = subtypeNode.properties[cleanPropName];
                if (propType) {
                  lst.push(propType);
                  if (LOG_TYPE_FLOW)
                    console.log(`elementAccess[union-object] ${propType} for ${cleanPropName} in edge ${cur}->${next}`);
                }
              }
            }
          }
          if (lst.length > 0) {
            source.get(next)!.set(cur, mergeTypes(lst));
          } else {
            console.warn(`Unexpected elementAccess when type ${tSet} : ${printType(tSet)} has no array or object subtype in edge ${cur}->${next}`);
          }
        } else {
          console.warn(`Unexpected elementAccess when type ${tSet} : ${printType(tSet)} is not array or object in edge ${cur}->${next}`);
        }
        setTypeVar(next, mergeBranches(next));
      }
      else if (edgeKind === "funcCall") {
        // 如果是函数调用，添加函数返回类型
        const typeNode = typeNodes.get(tSet);
        if (typeNode?.kind === "function") {
          source.get(next)!.set(cur, typeNode.returnType);
        } else {
          console.warn(`Unexpected funcCall when type ${tSet} : ${printType(tSet)} is not function in edge ${cur}->${next}`);
        }
        setTypeVar(next, mergeBranches(next));
      }
        



      // 控制流处理
      else if(edgeKind === "funcToArg") {
        const ty = typeNodes.get(tSet);
        const arg = find(Math.floor(next / 1000));
        const idx = next % 1000;
        let func;
        if (!ty) {
          console.error(`error: function Node ${syntaxNodes[cur].text}[${cur}] with null type!`);
          continue;
        }
        if (ty.kind === "union") {
          let f = ty.types.find(n => typeNodes.get(n)!.kind === "function");
          if (f) {
            const typeNode = typeNodes.get(f)!;
            if (typeNode.kind === "function") {
              func = typeNode.id;
              console.warn(`Unexpected Union type of function ${syntaxNodes[cur].text!}[${cur}], use initial node ${func}`);
            } else {
              console.error(`error: function Node ${syntaxNodes[cur].text}[${cur}] without function type!`);
              continue;
            }
          }
        }
        if (ty.kind === "function") {
          func = ty.id;
        }
        if (!func) {
          console.error(`error: function Node ${syntaxNodes[cur].text}[${cur}] without function type!`);
          continue;
        }
        const param = funcParam[func]?.[idx];
        if (!param) { 
          console.log(`Can not find Correspond param #${idx} of function ${syntaxNodes[func]?.text!}[${func}]`);
          continue;
        }

        // 擦除边，构建新边（默认function的id不会变）
        graph.get(cur)!.delete(next);
        graph.set(arg, graph.get(arg) ?? new Map());
        graph.get(arg)!.set(param, "ArgToParam");
        source.set(param, source.get(param) ?? new Map());
        source.get(param)!.set(arg, UNKNOWN);
        worklist.push(arg);
        continue;
      }
      else if (edgeKind === "makeArray") {
        // 如果是数组类型，添加元素类型
        if (nSet === undefined) {
          console.warn(`makeArray on undefined type in edge ${cur}->${next}`);
        } else {
          const typeNode = typeNodes.get(nSet);
          if (typeNode === undefined || typeNode.kind !== "array") {
            console.warn(`makeArray on non-array type ${printType(nSet)} in edge ${cur}->${next}`);
            continue;
          }
          const id = newTypeNode({ kind: "array", elementType: mergeTypes([typeNode.elementType, tSet]) });
          setTypeVar(next, id);
        }
      }
      else if (edgeKind === "initProperty") {
        // 如果是设置属性，添加属性类型
        const propName = syntaxNodes[cur]?.text;


        if (nSet === undefined) {
          console.warn(`initProperty on undefined type in edge ${cur}->${next}`);
          continue;
        }
        const typeNode = typeNodes.get(nSet);
        if (typeNode === undefined || typeNode.kind !== "object") {
          console.warn(`initProperty on non-object type ${printType(nSet)} in edge ${cur}->${next}`);
          continue;
        }
        if (!propName) {
          console.warn(`initProperty with no propName in edge ${cur}->${next}`);
          continue;
        }


        const id = newTypeNode({ kind: "object", name: typeNode.name, id: typeNode.id, properties: makePurePropertiesCopy(typeNode.properties, propName, tSet)});
        setTypeVar(next, id);
      }
      else if (edgeKind === "setProperty") {
        // 如果是设置属性，添加属性类型
        const propName = syntaxNodes[cur].text?.split(".").pop();

        if (!propName) {
          console.warn(`setProperty with no propName in edge ${cur}->${next}`);
          continue;
        }

        if (nSet === undefined) {
          console.warn(`setProperty on undefined type in edge ${cur}->${next}`);
          continue;
        }

        const typeNode = typeNodes.get(nSet);
        if (typeNode === undefined) continue;

        if (typeNode.kind === "object") {
          const dstty = typeNode?.kind === "object" ? typeNode.properties[propName!] ? mergeTypes([typeNode.properties[propName!], tSet]) : tSet : tSet;
          const id = newTypeNode({ kind: "object", name: typeNode.name, id: typeNode.id, properties: makePurePropertiesCopy(typeNode.properties, propName!, dstty) });
          setTypeVar(next, id);
        } else if (typeNode.kind === "union") {
          let updated = false;
          const newTypes = typeNode.types.map(t => {
            const tynd = typeNodes.get(t);
            if (tynd?.kind === "object") {
              const dstty = tynd.properties[propName!] ? mergeTypes([tynd.properties[propName!], tSet]) : tSet;
              const id = newTypeNode({ kind: "object", name: tynd.name, id: tynd.id, properties: makePurePropertiesCopy(tynd.properties, propName!, dstty) });
              updated = true;
              return id;
            } else {
              return t;
            }
          });
          if (updated) {
            setTypeVar(next, newTypeNode({ kind: "union", types: newTypes }));
          } else {
            console.warn(`setProperty on union type without object member ${printType(nSet)} in edge ${cur}->${next}`);
          }
        }
      }
      else if (edgeKind === "setElement") {
        // 取a[b]中的b
        const propName = syntaxNodes[cur].text?.split("[").pop()?.split("]").shift();
        if (!propName) {
          console.warn(`setElement with no propName in edge ${cur}->${next}`);
          continue;
        }

        if (nSet === undefined) {
          console.warn(`setElement on undefined type in edge ${cur}->${next}`);
          continue;
        }

        const typeNode = typeNodes.get(nSet);
        if (typeNode === undefined) continue;

        if (typeNode.kind === "object") {
          if (propName.startsWith('"') && propName.endsWith('"') || propName.startsWith("'") && propName.endsWith("'")) {
            const cleanPropName = propName.slice(1, -1);
            const dstty = typeNode?.kind === "object" ? typeNode.properties[cleanPropName] ? mergeTypes([typeNode.properties[cleanPropName], tSet]) : tSet : tSet;
            const id = newTypeNode({ kind: "object", name: typeNode.name, id: typeNode.id, properties: makePurePropertiesCopy(typeNode.properties, cleanPropName, dstty) });
            setTypeVar(next, id);
          }

        } else if (typeNode.kind === "array") {
          const idx = Number(propName);
          if (isNaN(idx)) {
            console.warn(`setElement with non-numeric index ${propName} in edge ${cur}->${next}`);
            continue;
          }
          const dstty = mergeTypes([typeNode.elementType, tSet]);
          const id = newTypeNode({ kind: "array", elementType: dstty });
          setTypeVar(next, id);
        } else if (typeNode.kind === "union") {
          let updated = false;
          const newTypes = typeNode.types.map(t => {
            const tynd = typeNodes.get(t);
            if (tynd?.kind === "object") {
              const dstty = tynd.properties[propName!] ? mergeTypes([tynd.properties[propName!], tSet]) : tSet;
              const id = newTypeNode({ kind: "object", name: tynd.name, id: tynd.id, properties: makePurePropertiesCopy(tynd.properties, propName!, dstty) });
              updated = true;
              return id;
            } else if (tynd?.kind === "array") {
              const idx = Number(propName);
              if (isNaN(idx)) {
                console.warn(`setElement with non-numeric index ${propName} in edge ${cur}->${next}`);
                return t;
              }
              const dstty = mergeTypes([tynd.elementType, tSet]);
              const id = newTypeNode({ kind: "array", elementType: dstty });
              updated = true;
              return id;
            } else {
              return t;
            }
          });
          if (updated) {
            setTypeVar(next, newTypeNode({ kind: "union", types: newTypes }));
          } else {
            console.warn(`setElement on union type without object or array member ${printType(nSet)} in edge ${cur}->${next}`);
          }
        }
      }
      else if (edgeKind === "setParamType") {
        // 如果是参数类型，添加参数类型
        const paramName = syntaxNodes[cur]?.text;


        if (nSet === undefined) {
          console.warn(`setParamType on undefined type in edge ${cur}->${next}`);
          continue;
        }
        const typeNode = typeNodes.get(nSet);
        if (typeNode === undefined || typeNode.kind !== "function") {
          console.warn(`setParamType on non-function type ${printType(nSet)} in edge ${cur}->${next}`);
          continue;
        }
        if (!paramName) {
          console.warn(`Parameter name not found in edge ${cur}->${next}`);
          continue;
        }


        // source[next][cur] = tSet;
        // let tylist : number[]  = [];
        // for(const srcStr in source[next]) {
        //   const src = Number(srcStr);
        //   const curParamName = syntaxNodes[src]?.text;
        //   if (curParamName !== paramName) continue;
        //   tylist.push(source[next][src]);
        // }
        setTypeVar(next, newTypeNode({ kind: "function", name: typeNode.name, id: typeNode.id, params: [...typeNode.params.filter(pa => pa.name !== paramName), {name: paramName, type: /* mergeTypes(tylist) */tSet}], returnType: typeNode.returnType }));
      }
      else if (edgeKind === "returnType" || edgeKind === "returnAnnotation") {
        if (edgeKind === "returnAnnotation" && syntaxNodes[cur].file && !path.relative(process.cwd(), syntaxNodes[cur].file).split(path.sep).includes("sdk")) continue;
        // 如果是返回类型，添加返回类型
        if (nSet === undefined) {
          console.warn(`returnType or returnAnnotation on undefined type in edge ${cur}->${next}`);
          continue;
        }
        const typeNode = typeNodes.get(nSet);
        if (typeNode === undefined || typeNode.kind !== "function") {
          console.warn(`returnType or returnAnnotation on non-function type ${printType(nSet)} in edge ${cur}->${next}`);
          continue;
        }

        source.get(next)!.set(cur, tSet);
        setTypeVar(next, newTypeNode({ kind: "function", name: typeNode.name, id: typeNode.id, params: typeNode.params, returnType: mergeBranches(next, ["returnType"/* , "returnAnnotation" */]) }));
      }




      // 更新传播
      if(typeSet.get(next) !== nSet && typeSet.get(next) !== UNKNOWN) worklist.push(next);
    }
  }

  // 传递sameID类型
  for (const [kind, a, b] of allConstraints) {
    if (kind === "sameID" && typeSet.get(b)) {
      setTypeVar(a, typeSet.get(b)!);
    }
  }

  const result: Record<string, string> = {};
  for (const [name, id] of globalVarBindings.entries()) {
    result[name] = printType(typeSet.get(id) ?? UNKNOWN);
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
    funcParam[rootX] = funcParam[rootY];
  }
}

// 合并标识符
function mergeIdentifiers() {
  for (const [kind, a, b] of allConstraints) {
    if (kind === "sameID") {
      // 合并标识符
      union(a, b);
    }
  }
}

// 验证 groundtruth
function evaluate() {
  console.log("========== Evaluating type graph consistency ==========");

  const result = {
    total: 0,
    correct: 0,
    wrong: 0,
    missing: 0,
    any: 0, // 统计any出现次数
    unknown: 0, // 统计无法判断类型的注释出现次数
    wrongEdges: [] as { kind: string, a: number, b: number, aType: string, bType: string }[],
  };

  // 遍历类型图中的所有约束
  for (const [kind, a, b] of allConstraints) {
    if (kind !== "annotation" && kind !== "returnAnnotation") continue;

    const aId = find(Number(a));
    const bId = find(Number(b));
    // 不统计库文件
    if (!syntaxNodes[aId].file || path.relative(process.cwd(), syntaxNodes[aId].file).split(path.sep).includes("sdk")) continue;
    result.total++;


    let aType =  printType(typeSet.get(aId) ?? UNKNOWN);
    if (kind === "returnAnnotation") {
      const ty = typeNodes.get(typeSet.get(aId) ?? UNKNOWN);
      if (ty && ty.kind === "function") {
        const retType = ty.returnType;
        aType = printType(retType)
      }
    }
    const bType = printType(typeSet.get(bId) ?? UNKNOWN);

    // === (1) 跳过 other 类型比较 ===
    const isAny = (t: string) => /^any(\[\])?$/.test(t);
    if (isAny(bType)) {
      result.any++;
      continue; // 不计入正确或错误
    } else if(bType === "unknown") {
      result.unknown++;
      console.log(`${[kind, a, b]}`)
      continue;
    }

    // === (2) 比较类型一致性 ===
    if (aType === "unknown") {
      result.missing++;
      result.wrongEdges.push({ kind, a: aId, b: bId, aType, bType });
      // console.warn(`[EVAL] Can not predict type on ${kind} edge ${aId}->${bId}, expected ${bType}`);
    } else if (aType === bType) {
      result.correct++;
      console.log(`[EVAL] Match on ${kind} edge ${syntaxNodes[aId].text}[${aId}]->${syntaxNodes[bId].text}[${bId}]: ${bType}`);
    } else {
      result.wrong++;
      result.wrongEdges.push({ kind, a: aId, b: bId, aType, bType });
      // console.warn(`[EVAL] Mismatch on ${kind} edge ${aId}->${bId}: inferred ${aType}, expected ${bType}`);
    }
  }

  // === (3) 输出汇总报告 ===
  const other = result.any + result.unknown;
  const acc = result.correct / Math.max(1, (result.total - other - result.missing));
  const cov = (result.correct + result.wrong) / (result.total - other);
  console.log("========== Evaluation Report ==========");
  console.log(`Total annotations: ${result.total}`);
  console.log(`Correct: ${result.correct}`);
  console.log(`Wrong: ${result.wrong}`);
  console.log(`Missing: ${result.missing}`);
  console.log(`Ignored: any * ${result.any} + unknown * ${result.unknown} = ${other}`);
  console.log(`coverage: ${(cov * 100).toFixed(2)}%`);
  console.log(`Effective accuracy: ${(acc * 100).toFixed(2)}%`);

  // === (4) 输出详细错误列表 ===
  if (result.wrongEdges.length > 0) {
    console.log("\n--- Type mismatches ---");
    for (const w of result.wrongEdges) {
      const aText = syntaxNodes[w.a]?.text ?? `(node ${w.a})`;
      const bText = syntaxNodes[w.b]?.text ?? `(node ${w.b})`;
      if (w.aType === "unknown") continue;
      console.log(
        `  [${w.kind}] ${aText}[${w.a}] (${w.aType})  !==  ${bText} (${w.bType})`
      );
    }
  }

  // === (5) 输出遗漏列表 ===
  if (result.wrongEdges.length > 0) {
    console.log("\n--- Type underived ---");
    for (const w of result.wrongEdges) {
      const aText = syntaxNodes[w.a]?.text ?? `(node ${w.a})`;
      const bText = syntaxNodes[w.b]?.text ?? `(node ${w.b})`;
      if (w.aType !== "unknown") continue;
      console.log(
        `  [${w.kind}] ${aText}[${w.a}] (${w.aType})  !==  ${bText} (${w.bType})`
      );
    }
  }

  return result;
}


// 输出图和约束
function emitGlobalTypeGraphAndConstraints() {
  const types = deriveVariableTypes();
  evaluate();

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

  // 写出类型标注结果
  const json = generateTypeAnno();
  const outfile = path.join(outputDir, "typeinfo.json");
  fs.writeFileSync(outfile, JSON.stringify(json, null, 2), "utf8");

  // 按 file 分组
  const groups : Record<string, any> = {};
  for (const item of json) {
    if (!groups[item.relapath]) groups[item.relapath] = [];
    const { file, relapath, ...rest } = item;  // 去掉 file 字段
    groups[item.relapath].push(rest);
  }

  for (const file in groups) {
    const outfile = path.join(path.join(outputDir, "typeinfo"), file + ".json");
    fs.mkdirSync(path.dirname(outfile), { recursive: true }); // 创建目录
    fs.writeFileSync(outfile, JSON.stringify(groups[file], null, 2), "utf8");
  }

  console.log(`Done. Output written to ${outDir}`);

  // ===== JSON 图生成函数 =====
  function generateTypeGraphJson(): { nodes: any[]; edges: any[] } {
    const nodes: any[] = [];
    const edges: any[] = [];
    const seen = new Set<number>();

    for (const [srcId, dsts] of graph) {
      const srcVar = syntaxNodes[srcId];
      const srcfile = syntaxNodes[srcId]?.file || "unknown";
      if (!seen.has(srcId)) {
        nodes.push({
          id: srcId,
          label: srcVar?.text || `var_${srcId}`,
          typeid: typeSet.get(srcId) ?? UNKNOWN,
          type: printType(typeSet.get(srcId) ?? UNKNOWN),
          fullType: printFullType(typeSet.get(srcId) ?? UNKNOWN),
          jsonType: printJsonType(typeSet.get(srcId) ?? UNKNOWN),
          text: srcVar?.text,
          file: srcfile.replace(".ast.json", "").replace(/\^/g, "\/").split("ast\/")[1],
          position: srcVar?.position,
        });
        seen.add(srcId);
      }

      for (const [dstId, edgeKind] of dsts) {
        const dstVar = syntaxNodes[dstId];
        const dstfile = syntaxNodes[dstId]?.file || "unknown";
        if (!seen.has(dstId)) {
          nodes.push({
            id: dstId,
            label: dstVar?.text || `var_${dstId}`,
            typeid: typeSet.get(dstId) ?? UNKNOWN,
            type: printType(typeSet.get(dstId) ?? UNKNOWN),
            fullType: printFullType(typeSet.get(dstId) ?? UNKNOWN),
            jsonType: printJsonType(typeSet.get(dstId) ?? UNKNOWN),
            text: dstVar?.text,
            file: dstfile.replace(".ast.json", "").replace(/\^/g, "\/").split("ast\/")[1],
            position: dstVar?.position,
          });
          seen.add(dstId);
        }

        edges.push({ from: srcId, to: dstId, label: edgeKind });
      }
    }

    return { nodes, edges };
  }


  function generateTypeAnno() {
    const outJson = [];
    for (const idstr in syntaxNodes) {
      const id = Number(idstr)
      const node = syntaxNodes[id];
      const t = printJsonType(typeSet.get(id) ?? UNKNOWN);
      if (t === "unknown" || !node.v8kind) continue;
      outJson.push({
        context: node.context,
        exprText: node.text,
        exprKind: node.v8kind,
        morphKind: node.kind,
        location: node.offset,
        pos: node.position,
        type: typeof(t) === "string" ? t : t.length === 1 ? t[0] : undefined,
        unionTypes: typeof(t) !== "string" && t.length > 1 ? t : undefined,
        relapath: node.file!.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, ""),
        file: path.join(node.file!.split("ast" + require("path").sep)[0].replace("_output", ""), node.file!.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "")),
      })
    }
    return outJson;
  }
}


// 主流程
function main() {
  // 创建一个虚拟节点，表示未知的导入
  syntaxNodes[0] = { kind: "null", text: "unknown import hole", file: "null", position: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }, offset: -1 };
  // 手动初始化内置类型节点
  typeNodes.set(NUMBER, { kind: "primitive", name: "number" });
  typeNodes.set(STRING, { kind: "primitive", name: "string" });
  typeNodes.set(BOOLEAN, { kind: "primitive", name: "boolean" });
  typeNodes.set(ANY, { kind: "primitive", name: "any" });
  typeNodes.set(UNKNOWN, { kind: "primitive", name: "unknown" });
  typeNodes.set(VOID, { kind: "primitive", name: "void" });
  typeNodes.set(NULL, { kind: "primitive", name: "null" });
  typeNodes.set(UNDEFINED, { kind: "primitive", name: "undefined" });
  typeNodes.set(NEVER, { kind: "primitive", name: "never" });
  typeNodes.set(REGEXP, { kind: "primitive", name: "RegExp" });
  typeNodes.set(BIGINT, { kind: "primitive", name: "bigint" });
  // 初始化类型集合
  setTypeVar(VOID, VOID)
  // 初始化typeNodeReverseMap
  for (const [id, node] of typeNodes.entries()) {
    typeNodeReverseMap.set(serializeTypeNode(node), Number(id));
  }


  const astFiles = getAstFiles(inputDir);
  for (const file of astFiles) {
    const ast = JSON.parse(fs.readFileSync(file, "utf8"));
    firstPass(file, ast);
  }
  // 控制台输出globalExportMap
  if (LOG_IMPORT)
    console.log("Global Export Map:", JSON.stringify(globalExportMap, null, 2));
  for (const file of astFiles) {
    secondPass(file, fileToAst[file]);
  }

  mergeIdentifiers();
  emitGlobalTypeGraphAndConstraints();
  analyzeIdentifierTypeFeatures();
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

// ===== 基于变量节点的类型特征分析 =====
function analyzeIdentifierTypeFeatures() {
  console.log("📊 Identifier Type Feature Analysis Starting...");

  const stats = {
    primitive: 0,
    object: 0,
    func: 0,
    array: 0,
    union: 0,
    unknown: 0,
    funcParamTotal: 0,
    funcCount: 0,
    crossFileRefs: 0,
    totalNodes: 0,
  };

  // 只保留 Identifier 节点
  const identifierNodes = Object.entries(syntaxNodes)
    .filter(([_, node]) => node.kind === "Identifier" && node.file && !path.relative(process.cwd(), node.file).split(path.sep).includes("sdk"))
    .map(([id]) => Number(id));

  for (const id of identifierNodes) {
    const tyId = typeSet.get(id) ?? UNKNOWN;
    const tyNode = typeNodes.get(tyId);

    stats.totalNodes++;
    if (!tyNode) {
      stats.unknown++;
    } else {
      switch (tyNode.kind) {
        case "primitive": if(tyNode.name !== "unknown") stats.primitive++; else stats.unknown++; break;
        case "object": stats.object++; break;
        case "function":
          stats.func++;
          stats.funcCount++;
          stats.funcParamTotal += tyNode.params?.length || 0;
          break;
        case "array": stats.array++; break;
        case "union": stats.union++; break;
      }
    }
  }

  // 跨文件引用统计：只要一条边跨文件，就算一次
  for (const [srcStr, dsts] of Object.entries(graph)) {
    const src = Number(srcStr);
    const srcFile = syntaxNodes[src]?.file;
    if (!srcFile) continue;

    for (const dstStr in dsts) {
      const dst = Number(dstStr);
      const dstFile = syntaxNodes[dst]?.file;
      if (!dstFile || srcFile === dstFile) continue;
      stats.crossFileRefs++;
    }
  }

  const result = {
    totalNodes: stats.totalNodes,
    primitive: { count: stats.primitive, percent: ((stats.primitive / stats.totalNodes) * 100).toFixed(1) },
    object: { count: stats.object, percent: ((stats.object / stats.totalNodes) * 100).toFixed(1) },
    function: { count: stats.func, percent: ((stats.func / stats.totalNodes) * 100).toFixed(1) },
    array: { count: stats.array, percent: ((stats.array / stats.totalNodes) * 100).toFixed(1) },
    union: { count: stats.union, percent: ((stats.union / stats.totalNodes) * 100).toFixed(1) },
    unknown: { count: stats.unknown, percent: ((stats.unknown / stats.totalNodes) * 100).toFixed(1) },
    "avg function params": (stats.funcParamTotal / (stats.funcCount || 1)).toFixed(2),
    "cross-file refs ": stats.crossFileRefs,
  };

  // 控制台输出
  console.log("========== Identifier Type Feature Report ==========");
  console.log(`Total Identifier nodes: ${result.totalNodes}`);
  for (const [k, v] of Object.entries(result)) {
    if (typeof v === "object") {
      console.log(`${k.padEnd(22)} ${v.count} nodes, ${v.percent}%`);
    } else {
      console.log(`${k.padEnd(22)} ${v}`);
    }
  }

  return result;
}
