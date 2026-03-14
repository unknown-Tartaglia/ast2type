import * as fs from "fs";
import * as path from "path";
import { Command } from "commander";
import { FactStore, Emitter, VarId } from "./ast2type/fact"
import { MetaStore } from "./ast2type/meta"
import { Solver } from "./ast2type/solver";
import { tNodeStore } from "./ast2type/nType";
import { DeterminantStrategy } from "./ast2type/strategy";
import { RuleStore } from "./ast2type/rule";

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
export const LOG_TYPENODE = false; // 是否开启类型节点日志
export const LOG_TYPENODE_VERBOSE = false; // 是否开启类型节点详细日志
const LOG_IDENTIFIER_NODE = false; // 是否开启标识符节点日志
const LOG_IMPORT = false; // 是否开启导入日志
export const LOG_TYPE_FLOW = false; // 是否开启类型流日志
const LOG_EVALUATE_STCS = false; // 是否评估groundtruth标注对比数据
const LOG_TYPE_STCS = false; // 是否开启类型统计
const LOG_OPERATOR_STCS = true; // 是否开启操作符统计（==, ===, !=, !==, !, typeof)
const IGNORE_WARNINGS = true; // 忽略警告
const IGNORE_ERRORS = false; // 忽略错误
const IGNORE_LOGS = false; // 忽略日志

export const DEDUCE_ONLY_WHEN_ALL_KNOWNN = false; // 仅在所有分支类型已知时进行类型推断

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
  | { kind: "literal"; value: string | number | boolean }
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
  offset: number;
}

// 全局结构
let typeVarCounter = 100;
const fileToAst: Record<string, AstNode> = {};
const globalExportMap: Record<string, Record<string, number>> = {};
const globalExportFa: Record<string, Record<string, string[]>> = {};
// const syntaxNodes: Record<number, { kind: string; text?: string; file?: string; position?: any; offset?: number; v8kind?:string; context?:string }> = {};
const typeNodes: Map<number, TypeNode> = new Map();
const allConstraints: Array<[string, number, number, string]> = [];
const globalVarBindings = new Map<string, number>();
const graph: Map<number, Map<number, string>> = new Map();
const source: Map<number, Map<number, number>> = new Map();
const parent: Record<number, number> = {};
const globalImportMap: Map<string, string> = new Map((() => { try { return JSON.parse(fs.readFileSync(path.join(inputDir, "importMap.json"), "utf8")); } catch { return []; } })());
let worklist: number[] = [];
const funcParam: Record<number, number[]> = {};
const constructors: Record<number, number> = {};
const tsMorphNodes = ["BigIntLiteral", "NumericLiteral", "FirstLiteralToken", "NullKeyword", "TrueKeyword", "FalseKeyword", "ObjectLiteralExpression",
  "ArrayLiteralExpression", "BinaryExpression", "PrefixUnaryExpression", "PostfixUnaryExpression", "TypeOfExpression", "RegularExpressionLiteral",
  "VoidExpression", "Identifier", "ThisKeyword", "ConditionalExpression", "PropertyAccessExpression", "ElementAccessExpression", "CallExpression",
  "ArrowFunction", "FunctionExpression", "ReturnStatement", "ParenthesizedExpression", "TemplateExpression", "NewExpression"];
const start = Date.now();
const console_methods = ["log", "error", "warn", "info"] as const;
const operator_cnts : Map<string, number> = new Map();
const operands : Map<string, Set<number>> = new Map();

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
  let ignores : string[] = [];
  if (IGNORE_ERRORS) ignores = ignores.concat(["error"]);
  if (IGNORE_WARNINGS) ignores = ignores.concat(["warn"]);
  if (IGNORE_LOGS) ignores = ignores.concat(["log"]);
  if (ignores.includes(m)) {
    console[m] = (...args: any[]) => {};
    continue;
  }

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

function allocateTypeNode(t: TypeNode): number {
  const id = typeVarCounter++;
  const serialized = serializeTypeNode(t);
  typeNodes.set(id, t);
  typeNodeReverseMap.set(serialized, id);
  if (LOG_TYPENODE) {
    console.log(`New type node created: ${id} : ${printFullType(id)}`);
  }
  return id;
}

// 修改TypeNode，危险操作，传播影响
function modifyTypeNode(id: number, t: TypeNode) {
  if (LOG_TYPENODE) {
    console.log(`Change type node ${id} from ${JSON.stringify(typeNodes.get(id)!) } to ${JSON.stringify(t)}`);
  }
  typeNodes.set(id, t);
  typeNodeReverseMap.set(serializeTypeNode(t), id);
  // 传播影响
  const affected = typeNodeUsers.get(id);
  if (affected) {
    for (const id of affected) {
      worklist.push(id);
    }
  }
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
      case "literal":
        return `literal:${t.value}`;
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
    case "literal":
      ret = `literal:${t.value}`;
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

export function newTypeNode(ty: TypeNode): number{
  if (LOG_TYPENODE_VERBOSE)
    console.log(`allocating new type node: ${JSON.stringify(ty)} ~~~ ${serializeTypeNode(ty)}`);
  let serialized = serializeTypeNode(ty);
  if (typeNodeReverseMap.has(serialized)) {
    const id = typeNodeReverseMap.get(serialized);
    return id!;
  }

  // 处理对象类型的循环引用
  const occur: Record<string, number> = Object.create(null);
  return ["object", "function"].includes(ty.kind) ? helper(ty) : allocateTypeNode(ty);
  function helper(t: TypeNode): number {
    if (!t) {
      // if (LOG_TYPENODE)
        console.warn(`Undefined typeNode in newTypeNode`);
      return UNKNOWN; // 返回UNKNOWN
    }
    if (t.kind === "array") t.elementType = helper(typeNodes.get(t.elementType)!);
    else if (t.kind === "function") {
      if (occur[t.id] !== undefined) {
        occur[t.id] = newTypeNode(t)
        return occur[t.id];
      }
      occur[t.id] = UNKNOWN;

      for (const param of t.params) {
        param.type = helper(typeNodes.get(param.type)!);
      }
      t.returnType = helper(typeNodes.get(t.returnType)!);

      if (occur[t.id] !== UNKNOWN && serializeTypeNode(typeNodes.get(occur[t.id])!) !== serializeTypeNode(t)) {
        modifyTypeNode(occur[t.id], t);
        return occur[t.id];
      }
    } else if (t.kind === "union") {
      t.types = t.types.map(ty => helper(typeNodes.get(ty)!));
    } else if (t.kind === "object") {
      // console.log(`enter ${t.name}`)
      if (occur[t.id]) {
        occur[t.id] = newTypeNode(t)
        return occur[t.id];
      }
      occur[t.id] = UNKNOWN;

      for (const key in t.properties) {
        t.properties[key] = helper(typeNodes.get(t.properties[key])!);
      }

      if (occur[t.id] !== UNKNOWN && serializeTypeNode(typeNodes.get(occur[t.id])!) !== serializeTypeNode(t)) {
        modifyTypeNode(occur[t.id], t);
        return occur[t.id];
      }
      // console.log(`exit ${t.name}`)
      // t.properties = Object.create(null);
    }
    serialized = serializeTypeNode(t);
    if (typeNodeReverseMap.has(serialized)) {
      const id = typeNodeReverseMap.get(serialized)!;
      return id;
    } else return allocateTypeNode(t);
  }
}

function mergeTypes(tys: number[]) : number {
  let tyList : number[] = [], ret : number, has_unknown = false, arrList = []; 
  const tmp = tys.map(ty => { const typeNode = typeNodes.get(ty); return typeNode?.kind === "union" ? [...typeNode.types] : [ty] }).flat();
  const set = new Set(tmp.filter(ty => ty !== UNKNOWN));
  if (tmp.includes(UNKNOWN)) {
    // 保护，存在unknown就不推导Literal
    has_unknown = true;
    if(DEDUCE_ONLY_WHEN_ALL_KNOWNN)  return UNKNOWN;
  }
  for (const ty of set) {
    const typeNode = typeNodes.get(ty);
    let cand = ty;
    if (typeNode?.kind === "literal" && (set.size > 1 || has_unknown)) cand = typeof typeNode.value === "number" ? NUMBER : typeof typeNode.value === "string" ? STRING : BOOLEAN;
    if (typeNode?.kind === "array") {
      arrList.push(cand);
      continue;
    }
    tyList.push(cand);
  }
  if (arrList.length > 1) arrList = [newTypeNode( { kind: "array", elementType: ANY})];
  tyList = [...new Set(tyList), ...arrList]; // 去重

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

const meta = new MetaStore();
const tNode = new tNodeStore();
const rule = new RuleStore();
const fact = new FactStore();
const emit = new Emitter(fact);
const dtmStrtgy = new DeterminantStrategy();
const solver = new Solver(rule, dtmStrtgy);

// 第一遍：标号并提取export
function firstPass(filePath: string, ast: AstNode) {
  function walk(node: AstNode) {
    node.varId = getTypeVarId(node);
    // 提前函数声明
    for (const child of node.children || []) {
      child.parent = node;
      walk(child);
    }

    // 还原filepath中的^为\\
    let realPath = path.basename(filePath).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");

    // export Class Enum TypeAlias Interface
    const exportedKinds = ["ClassDeclaration", "InterfaceDeclaration", "EnumDeclaration", "TypeAliasDeclaration", "FunctionDeclaration"];
    if (exportedKinds.includes(node.kind) && findNodesByKind(node, "ExportKeyword").length > 0) {
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
        for (const idNode of idNodes) 
          if (idNode.children && idNode.children.length > 0 && idNode.children[0].kind === "Identifier" && idNode.children[0].text){
            globalExportMap[realPath] ??= {};
            globalExportMap[realPath][idNode.children[0].text] = idNode.children[0].varId!;
            if (idNode.children.length === 3 && idNode.children[1].kind === "FirstAssignment")
              emit.flow(idNode.children[2].varId!, idNode.children[0].varId!, idNode.text);
        }
        // 处理default
        if (dftkwd && idNodes.length === 1) {
          const idNode = idNodes[0];
          if (idNode.children && idNode.children.length > 0 && idNode.children[0].kind === "Identifier" && idNode.children[0].text) {
            globalExportMap[realPath] ??= {};
            globalExportMap[realPath][dftkwd.text!] = dftkwd.varId!;
            emit.flow(idNode.children[0].varId!, dftkwd.varId!, "default keyword");
            // allConstraints.push(["sameType", dftkwd.varId!, idNodes[0].varId!, "default keyword"]);
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
                emit.flow(idNode.children[0].varId!, idNode.children[2].varId!, `${idNode.text}`);
              } else if (idNode.children && idNode.children.length === 1 && idNode.children[0].kind === "Identifier" && idNode.children[0].text) {
                globalExportMap[realPath][idNode.children[0].text] = idNode.children[0].varId!;
              }
          }
        }
      }
      if (dftkwd) {
        globalExportMap[realPath] ??= {};
        globalExportMap[realPath][dftkwd.text!] = dftkwd.varId!;
        emit.flow(idNode.varId!, dftkwd.varId!, "default keyword");
        // allConstraints.push(["sameType", dftkwd.varId!, idNode.varId!, "default keyword"]);
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
  let unprocsdScopes: Map<string, Set<number>>[] = [];
  let unprocsdVars = new Map<string, Set<number>>();

  const preOrderHandlers: Record<string, (node: AstNode) => void> = {
    // 处理匿名对象
    ObjectLiteralExpression(node) {
      meta.v8Kind.set(node.varId!, "ObjectLiteral");  
      // syntaxNodes[node.varId!].v8kind = "ObjectLiteral"
      emit.allocObj(node.varId!);
      // const typeId = newTypeNode({ kind: "object", name: `anonymous${node.varId!}`, id: node.varId!, properties: Object.create(null) });
      // allConstraints.push(["hasType", node.varId!, typeId, `new object`]);
    },
    // 处理函数声明
    FunctionDeclaration(node) {
      if (node.children) {
        const idNode = node.children?.find(n => n.kind === "Identifier");
        if (idNode && idNode.varId !== undefined && idNode.text) {
          varBindings.set(idNode.text, idNode.varId!);
          meta.funcName.set(node.varId!, idNode.text);
          emit.allocFunction(node.varId!, idNode.varId);
          if (node.varId !== idNode.varId) {
              meta.funcBindMap.set(idNode.varId, node.varId!);
          }
        }


        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            emit.returnAnnot(idNode!.varId!, typeNode.varId!);
            // const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: UNKNOWN });
            // setTypeVar(idNode?.varId!, id);
            // allConstraints.push(["returnAnnotation", idNode?.varId!, typeNode.varId, `return type of function ${idNode?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          emit.returnVoid(node.varId!);
          // const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: VOID });
          // setTypeVar(idNode?.varId!, id);
        }
        // else {
        //   const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: UNKNOWN });
        //   setTypeVar(idNode?.varId!, id);
        // }
      }
    },
    FunctionExpression(node) {
      meta.v8Kind.set(node.varId!, "FunctionLiteral");
      // syntaxNodes[node.varId!].v8kind = "FunctionLiteral";
      emit.allocFunction(node.varId!, node.varId!);
      if (node.children) {
        const idNode = node;
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            emit.returnAnnot(idNode!.varId!, typeNode.varId!);
            // const id = newTypeNode({ kind: "function", name: idNode?.text!, id: idNode?.varId!, params: [], returnType: UNKNOWN });
            // setTypeVar(idNode?.varId!, id);
            // allConstraints.push(["returnAnnotation", idNode?.varId!, typeNode.varId, `return type of function ${idNode?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          emit.returnVoid(idNode!.varId!);
          // const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: idNode?.varId!, params: [], returnType: VOID });
          // setTypeVar(idNode?.varId!, id);
        }
        // else {
        //   const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: idNode?.varId!, params: [], returnType: UNKNOWN });
        //   setTypeVar(idNode?.varId!, id);
        // }
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
          emit.annot(left.varId!, typeNode.varId!);
          // allConstraints.push(["annotation", left.varId, typeNode.varId, `annotation ${left.text!} : ${typeNode.text!}`]);
        }
      }
      // 处理赋值操作
      if (firstAssignmentIndex && firstAssignmentIndex !== -1) {
        const right = node.children?.[firstAssignmentIndex + 1];
        meta.v8Kind.set(node.varId!, "Assignment");
        meta.offset.set(node.varId!, right?.offset!);
        // syntaxNodes[node.varId!].v8kind = "Assignment";
        // syntaxNodes[node.varId!].offset = right?.offset;
        if (left.varId !== undefined && right?.varId !== undefined) {
          emit.flow(right.varId!, left.varId!, `variable ${left.text!} = ${right.text!}`);
          // allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
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

      emit.alias(right.varId!, left.varId!);
      // allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);

      //处理namespace
      let paNode = node.parent?.parent?.parent;
      if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
      paNode = paNode.children?.find(n => n.kind === "Identifier");
      if (!paNode) return;
      if (left.text) meta.propName.set(left.varId!, left.text);
      emit.prop(paNode.varId!, left.varId!);
      // allConstraints.push(["initProperty", paNode.varId!, left.varId!, `${paNode.text!}.${left.text!}`]);
      // allConstraints.push(["takeProperty", left.varId!, paNode.varId!, `${paNode.text!}.${left.text!}`]);
    },
    // 处理函数参数
    Parameter(node) {
      if (node.children) {
        const paramIdNode = node.children?.find(n => n.kind === "Identifier");
        if (!paramIdNode || !paramIdNode.varId) return;
        paramBindings.set(paramIdNode.text!, paramIdNode.varId!);
        meta.paramName.set(paramIdNode.varId!, paramIdNode.text!);

        // 处理类型注解
        const colonIndex = node.children?.findIndex(n => n.kind === "ColonToken");
        if (colonIndex !== undefined && colonIndex !== -1) {
          const typeNode = node.children?.[colonIndex + 1];
          if (typeNode && typeNode.varId) {
            emit.annot(paramIdNode.varId!, typeNode.varId!);
            // allConstraints.push(["annotation", paramIdNode.varId!, typeNode.varId, `annotation ${paramIdNode.text!} : ${typeNode.text!}`]);
          }
        }
        
        // 处理初始化
        const equalIndex = node.children?.findIndex(n => n.kind === "FirstAssignment");
        if (equalIndex !== undefined && equalIndex !== -1) {
          const right = node.children?.[equalIndex + 1];
          if (right && right.varId) {
            emit.flow(right.varId!, paramIdNode.varId!, `parameter ${paramIdNode.text!} = ${right.text!}`);
            // allConstraints.push(["sameType", paramIdNode.varId!, right.varId, `parameter ${paramIdNode.text!} = ${right.text!}`]);
          }
        }

        let funcIdNode = node.parent;
        while (funcIdNode && !["FunctionDeclaration", "MethodDeclaration", "MethodSignature", "ArrowFunction", "Constructor", "FunctionExpression"].includes(funcIdNode.kind)) funcIdNode = funcIdNode.parent;
        if (!funcIdNode || !funcIdNode.varId) return;

        const params = node.parent?.children?.filter(n => n.kind === "Parameter") || [];
        const index = params.findIndex(p => p === node);
        emit.param(funcIdNode.varId!, paramIdNode.varId!, index)
        meta.paramIndex.set(paramIdNode.varId!, index)
        if (!meta.funcParamMap.has(funcIdNode.varId!)) {
            meta.funcParamMap.set(funcIdNode.varId!, new Map<number, VarId>())
        }
        meta.funcParamMap.get(funcIdNode.varId!)!.set(index, paramIdNode.varId!)

        // allConstraints.push(["setParamType", funcIdNode.varId!, paramIdNode.varId!, `parameter ${paramIdNode.text!} in function ${funcIdNode.text!}`]);
        // if (!funcParam[funcIdNode.varId]) funcParam[funcIdNode.varId] = [];
        // funcParam[funcIdNode.varId].push(paramIdNode.varId);
      }
    },
    // 处理枚举声明
    EnumDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId !== undefined) {
          meta.enumName.set(idNode.varId!, idNode.text!);
          emit.allocEnum(idNode.varId!);
          // const typeId = newTypeNode({ kind: "enum", name: idNode.text!, members: {} });
          // setTypeVar(idNode.varId!, typeId);
          varBindings.set(idNode.text!, idNode.varId!);
        }

        //处理namespace
        let paNode = node.parent?.parent?.parent;
        if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
        paNode = paNode.children?.find(n => n.kind === "Identifier");
        if (!paNode) return;
        if (idNode.text) meta.propName.set(idNode.varId!, idNode.text);
        emit.prop(paNode.varId!, idNode.varId!);
        // allConstraints.push(["initProperty", paNode.varId!, idNode.varId!, `${paNode.text!}.${idNode.text!}`]);
        // allConstraints.push(["takeProperty", idNode.varId!, paNode.varId!, `${idNode.text!}.${paNode.text!}`]);
      }
    },
    // 处理枚举成员
    EnumMember(node) {
      const idNode = node.children?.find(n => n.kind === "Identifier");
      const paNode = findParentByKind(node, "EnumDeclaration")?.children?.find(n => n.kind === "Identifier");
      const nb = node.children?.find(n => n.kind === "FirstLiteralToken");
      if(!paNode || !paNode.varId || !idNode || !idNode || !nb?.text) return;
      varBindings.set(idNode.text!, idNode.varId!);

      emit.enumMember(paNode.varId!, idNode.varId!);
      emit.flow(nb.varId!, idNode.varId!, `enum member ${idNode.text} = ${nb.text}`);
      // const oldTypeId = typeSet.get(paNode.varId!);
      // if (!oldTypeId) return;
      // const oldTypeNode = typeNodes.get(oldTypeId);
      // if (!oldTypeNode || oldTypeNode.kind !== "enum") return;
      // const newMembers = { ...oldTypeNode.members };
      // newMembers[idNode.text!] = newTypeNode({ kind: "primitive", name: nb.text});

      // const typeId = newTypeNode({ kind: "enum", name: idNode.text!, members: newMembers });
      // setTypeVar(paNode.varId!, typeId);
    },
    // 处理接口声明
    InterfaceDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId !== undefined) {
          emit.allocInterface(idNode.varId!);
          // const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
          // setTypeVar(idNode.varId!, typeId);
          varBindings.set(idNode.text!, idNode.varId!);
        }

        //处理namespace
        let paNode = node.parent?.parent?.parent;
        if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
        paNode = paNode.children?.find(n => n.kind === "Identifier");
        if (!paNode) return;
        if (idNode.text) meta.propName.set(idNode.varId!, idNode.text);
        emit.prop(paNode.varId!, idNode.varId!);
        // allConstraints.push(["initProperty", paNode.varId!, idNode.varId!, `${paNode.text!}.${idNode.text!}`]);
        // allConstraints.push(["takeProperty", idNode.varId!, paNode.varId!, `${idNode.text!}.${paNode.text!}`]);
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
            if (propIdNode.text) meta.propName.set(propIdNode.varId!, propIdNode.text);
            emit.prop(idNode.varId!, propIdNode.varId!);
            emit.annot(propIdNode.varId!, typeNode.varId!);
            // allConstraints.push(["initProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
            // allConstraints.push(["takeProperty", propIdNode.varId!, idNode.varId!, `${propIdNode.text!}.${idNode.text!}`]);
            // allConstraints.push(["annotation", propIdNode.varId, typeNode.varId, `annotation ${idNode.text!}.${propIdNode.text!} : ${typeNode.text!}`]);
          }
        } else {
          if (propIdNode.text) meta.propName.set(propIdNode.varId!, propIdNode.text);
          emit.prop(idNode.varId!, propIdNode.varId!);
          // allConstraints.push(["initProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
          // allConstraints.push(["takeProperty", propIdNode.varId!, idNode.varId!, `${propIdNode.text!}.${idNode.text!}`]);
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

        // let funcType: TypeNode = { kind: "function", name: methodIdNode?.text!, id: methodIdNode?.varId!, params: [], returnType: UNKNOWN };
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            emit.returnAnnot(methodIdNode.varId!, typeNode.varId!);
            // allConstraints.push(["returnAnnotation", methodIdNode.varId, typeNode.varId, `return type of method ${idNode.text!}`]);
          }
        } else {
          // funcType.returnType = UNKNOWN;
        }

        meta.funcName.set(node.varId!, methodIdNode.text!);
        emit.allocFunction(node.varId!, methodIdNode.varId!);
        if (node.varId !== methodIdNode.varId) {
            meta.funcBindMap.set(methodIdNode.varId!, node.varId!);
        }
        if (methodIdNode.text) meta.propName.set(methodIdNode.varId!, methodIdNode.text);
        emit.prop(idNode.varId!, methodIdNode.varId!);
        // const typeId = newTypeNode(funcType);
        // setTypeVar(methodIdNode.varId!, typeId);

        // allConstraints.push(["initProperty", idNode.varId, methodIdNode.varId, `${idNode.text}.${methodIdNode.text!}`]);
        // allConstraints.push(["takeProperty", methodIdNode.varId!, idNode.varId!, `${methodIdNode.text!}.${idNode.text!}`]);
      }
    },
    // 处理class声明
    ClassDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId) {
          // const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
          // if (LOG_IDENTIFIER_NODE)
          //   console.log(`Class ${idNode.text} has type ID ${typeId}`);
          // setTypeVar(idNode.varId!, typeId);
          emit.allocClass(idNode.varId!);
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

        if (propIdNode.text) meta.propName.set(propIdNode.varId!, propIdNode.text);
        console.log(`PropertyDeclaration: ${idNode.text!}.${propIdNode.text!}`);
        emit.prop(idNode.varId, propIdNode.varId);
        // allConstraints.push(["initProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
        // allConstraints.push(["takeProperty", propIdNode.varId!, idNode.varId!, `${propIdNode.text!}.${idNode.text!}`]);
        

        const colonNode = node.children.find(n => n.kind === "ColonToken");
        const equalNode = node.children.find(n => n.kind === "FirstAssignment");


        // 处理类型注解
        if (colonNode && colonNode.varId) {
          const index = node.children?.findIndex(n => n.kind === "ColonToken");
          if (index !== undefined && index !== -1) {
            const typeNode = colonNode!.parent!.children?.[index + 1];
            if (typeNode && typeNode.varId) {
              emit.annot(propIdNode.varId!, typeNode.varId!);
              // allConstraints.push(["annotation", propIdNode.varId, typeNode.varId, `annotation ${idNode.text!}.${propIdNode.text!} : ${typeNode.text!}`]);
            }
          }
        }

        // 处理初始化
        if (equalNode && equalNode.varId) {
          const index = node.children?.findIndex(n => n.kind === "FirstAssignment");
          if (index !== undefined && index !== -1) {
            const right = node.children?.[index + 1];
            if (right && right.varId) {
              emit.flow(right.varId!, propIdNode.varId!, `property ${idNode.text!}.${propIdNode.text!} = ${right.text!}`);
              // allConstraints.push(["sameType", propIdNode.varId, right.varId, `${idNode.text!}.${propIdNode.text!} = ${right.text!}`]);
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

          // let funcType: TypeNode = { kind: "function", name: propIdNode?.text!, id: propIdNode?.varId!, params: [], returnType: UNKNOWN };
          const index = node.children?.findIndex(n => n.kind === "ColonToken");
          // 类型注解
          if (index !== undefined && index !== -1) {
            const typeNode = node.children?.[index + 1];
            if (typeNode && typeNode.varId) {
              emit.returnAnnot(propIdNode.varId!, typeNode.varId!);
              // allConstraints.push(["returnAnnotation", propIdNode.varId, typeNode.varId, `return type of method ${idNode.text!}`]);
            }
          } else if (findNodesByKind(node, "ReturnStatement").length === 0) {
            // 如果没有返回类型注解并且没有Return语句
            // funcType.returnType = VOID;
            emit.returnVoid(node.varId!);
          } else {
            // funcType.returnType = UNKNOWN;
          }

          meta.funcName.set(node.varId!, propIdNode.text!);
          emit.allocFunction(node.varId!, propIdNode.varId!);
          if (node.varId !== propIdNode.varId) {
              meta.funcBindMap.set(propIdNode.varId!, node.varId!);
          }
          if (propIdNode.text) meta.propName.set(propIdNode.varId!, propIdNode.text);
          emit.prop(idNode.varId!, propIdNode.varId!);
          // //
          // const typeId = newTypeNode(funcType);
          // setTypeVar(propIdNode.varId!, typeId);

          // allConstraints.push(["initProperty", idNode.varId, propIdNode.varId, `${idNode.text}.${propIdNode.text!}`]);
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

        console.log(node.text);
        constructors[idNode.varId] = node?.varId!;
        emit.allocFunction(node.varId!, node.varId!);
        meta.propName.set(node.varId!, "constructor");
        emit.prop(idNode.varId!, node.varId!);
        // let funcType: TypeNode = { kind: "function", name: propIdNode?.text!, id: propIdNode?.varId!, params: [], returnType: VOID };
        // const typeId = newTypeNode(funcType);
        // setTypeVar(propIdNode.varId!, typeId);

        // allConstraints.push(["initProperty", idNode.varId, propIdNode.varId, `${idNode.text}.${propIdNode.text!}`]);
      }
    },
    // 处理模块声明
    ModuleDeclaration(node) {
      const idNode = node.children?.find(n => n.kind === "Identifier");

      if(idNode && idNode.varId) {
        emit.allocObj(idNode.varId!);
        // const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
        // setTypeVar(idNode.varId!, typeId);
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
        emit.allocObj(idNode.varId!);
        // const typeId = newTypeNode({ kind: "object", name: idNode.text!, id: idNode.varId!, properties: Object.create(null) });
        // setTypeVar(idNode.varId!, typeId);
        varBindings.set(idNode.text, idNode.varId);

        if (!resolvedFile) {
          emit.flow(0, idNode.varId!, `Failed import ${idNode.text} from ${moduleSpecifier}`);
          // allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
        } else {
          for (const symb in globalExportMap[resolvedFile]) {
            meta.propName.set(globalExportMap[resolvedFile][symb], symb);
            emit.prop(idNode.varId!, globalExportMap[resolvedFile][symb]);
            // allConstraints.push(["initProperty", idNode.varId!, globalExportMap[resolvedFile]?.[symb], `${idNode.text!}.${symb}`]);
            // allConstraints.push(["takeProperty", globalExportMap[resolvedFile]?.[symb], idNode.varId!, ``]);
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
            emit.flow(0, idNode.varId!, `Failed import ${idNode.text} from ${moduleSpecifier}`);
            // allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
          } else {
            target = globalExportMap[resolvedFile]?.[idNode.text!];
          }
        } else if(ndimpt.children?.length === 3) {
          idNode = ndimpt.children[2];
          varBindings.set(idNode.text!, idNode.varId!);

          if (!resolvedFile) {
            emit.flow(0, idNode.varId!, `Failed import ${idNode.text} from ${moduleSpecifier}`);
            // allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
          } else {
            target = globalExportMap[resolvedFile]?.[ndimpt.children[0].text!];
          }
        }

        if (target !== undefined && idNode) {
          emit.flow(target, idNode.varId!, `Success import ${idNode.text} from ${moduleSpecifier}`);  
          // allConstraints.push(["sameType", idNode.varId!, target, `Success import ${idNode.text} from ${moduleSpecifier}`]);
        }
      }

      // import x from "xxx"
      const impt = findNodesByKind(node, "ImportClause")[0];
      for (const idNode of impt?.children?.filter(c => c.kind === "Identifier") || []) {
        varBindings.set(idNode.text!, idNode.varId!);

        if (!resolvedFile) {
          emit.flow(0, idNode.varId!, `Failed import ${idNode.text} from ${moduleSpecifier}`);
          allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${idNode.text} from ${moduleSpecifier}`]);
        } else {
          const target = globalExportMap[resolvedFile]?.[idNode.text!] === undefined? globalExportMap[resolvedFile]?.["default"] : globalExportMap[resolvedFile]?.[idNode.text!];
          if (target !== undefined) {
            emit.flow(target, idNode.varId!, `Success import ${idNode.text} from ${moduleSpecifier}`);
            // allConstraints.push(["sameType", idNode.varId!, target, `Success import ${idNode.text} from ${moduleSpecifier}`]);
          }
        }
      }
    },
    // 处理export xxx from xxx
    ExportDeclaration(node) {
      const raw = node.children?.find(n => n.kind === "StringLiteral")?.text;
      const moduleSpecifier = raw?.replace(/^['"]|['"]$/g, ""); // 去掉引号
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
              emit.flow(0, idNode.varId!, `Failed import ${symbol} from ${moduleSpecifier}`);
              // allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
              continue;
            }

            const target = globalExportMap[resolvedFile]?.[symbol] === undefined? globalExportMap[resolvedFile]?.["default"] : globalExportMap[resolvedFile]?.[symbol];
            if (target !== undefined) {
              emit.flow(target, idNode.varId!, `Success import ${symbol} from ${moduleSpecifier}`);
              // allConstraints.push(["sameType", idNode.varId!, target, `Success import ${symbol} from ${moduleSpecifier}`]);
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
                emit.flow(ret, idNode.varId!, `Asesome! Success import ${symbol}(*) from ${moduleSpecifier}`);
                // allConstraints.push(["sameType", idNode.varId!, ret, `Asesome! Success import ${symbol}(*) from ${moduleSpecifier}`]);
              } else {
                if (LOG_IMPORT)
                  console.warn(`Symbol ${symbol} not found in export map of ${resolvedFile} in ${filePath}`);
                emit.flow(0, idNode.varId!, `Failed import ${symbol} from ${moduleSpecifier}`);
                // allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
              }
            }
          }
      }
    }
  }

  const handlers: Record<string, (node: AstNode) => void> = {
    StringLiteral(node) {
      emit.allocLiteral(node.varId!, node.text ?? "unknown text", STRING);
      // allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: node.text?.replace(/^['"`]|['"`]$/g, "") ?? "unknown text"}), `${node.text!} ∈ string`]);
      // syntaxNodes[node.varId!].v8kind = "Literal"
      meta.v8Kind.set(node.varId!, "Literal");
    },
    NoSubstitutionTemplateLiteral(node) {
      emit.allocLiteral(node.varId!, node.text ?? "unknown text", STRING);
      // allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: node.text?.replace(/^['"`]|['"`]$/g, "") ?? "unknown text"}), `${node.text!} ∈ string`]);
    },
    FirstLiteralToken(node) {
      // 暂时默认为数字
      emit.allocLiteral(node.varId!, Number(node.text), NUMBER);
      // allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: Number(node.text)}), `${node.text!} ∈ number`]);
      // syntaxNodes[node.varId!].v8kind = "Literal"
      meta.v8Kind.set(node.varId!, "Literal");
    },
    NumericLiteral(node) {
      emit.allocLiteral(node.varId!, Number(node.text), NUMBER);
      // allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: Number(node.text)}), `${node.text!} ∈ number`]);
      // syntaxNodes[node.varId!].v8kind = "Literal"
      meta.v8Kind.set(node.varId!, "Literal");
    },
    TrueKeyword(node) {
      emit.allocLiteral(node.varId!, true, BOOLEAN);
      // allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: true}), `${node.text!} ∈ boolean`]);
      // syntaxNodes[node.varId!].v8kind = "Literal"
      meta.v8Kind.set(node.varId!, "Literal");
    },
    FalseKeyword(node) {
      emit.allocLiteral(node.varId!, false, BOOLEAN);
      // allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: false}), `${node.text!} ∈ boolean`]);
      // syntaxNodes[node.varId!].v8kind = "Literal"
      meta.v8Kind.set(node.varId!, "Literal");
    },
    NullKeyword(node) {
      emit.allocLiteral(node.varId!, null, NULL);
      // allConstraints.push(["hasType", node.varId!, NULL, `${node.text!} ∈ null`]);
      // syntaxNodes[node.varId!].v8kind = "Literal"
      meta.v8Kind.set(node.varId!, "Literal");
    },
    BigIntLiteral(node) {
      emit.allocLiteral(node.varId!, BigInt(node.text ?? "0"), BIGINT);
      // allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: Number(node.text)}), `${node.text!} ∈ number`]);
      // syntaxNodes[node.varId!].v8kind = "Literal"
      meta.v8Kind.set(node.varId!, "Literal");
    },
    RegularExpressionLiteral(node) {
      emit.allocLiteral(node.varId!, new RegExp(node.text?.slice(1, node.text.lastIndexOf("/")) || ""), REGEXP);
      // allConstraints.push(["hasType", node.varId!, REGEXP, `${node.text!} ∈ RegExp`]);
      // syntaxNodes[node.varId!].v8kind = "RegExpLiteral"
      meta.v8Kind.set(node.varId!, "RegExpLiteral");
    },
    ArrayLiteralExpression(node) {
      // syntaxNodes[node.varId!].v8kind = "ArrayLiteral"
      meta.v8Kind.set(node.varId!, "ArrayLiteral");
      emit.allocArray(node.varId!);
      // setTypeVar(node.varId!, newTypeNode({ kind: "array", elementType: UNKNOWN }));
      for (const child of node.children?.find(c => c.kind === "SyntaxList")?.children?.filter(c => c.kind !== "CommaToken") || []) {
        emit.arrayElement(node.varId!, child.varId!);
        // allConstraints.push(["makeArray", node.varId!, child.varId!, `element ${child.text!} of array ${node.text!}`]);
      }
    },
    TemplateExpression(node) {
      emit.allocLiteral(node.varId!, node.text ?? "", STRING);
      // allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
      // syntaxNodes[node.varId!].v8kind = "TemplateLiteral";
      meta.v8Kind.set(node.varId!, "TemplateLiteral");
    },
    FirstTemplateToken(node) {
      emit.allocLiteral(node.varId!, node.text ?? "", STRING);
      // allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
      // syntaxNodes[node.varId!].v8kind = "TemplateLiteral";
      meta.v8Kind.set(node.varId!, "TemplateLiteral");
    },
    // 处理类型关键字
    NumberKeyword(node) {
      if (node.varId === undefined) return;
      emit.allocPrimitive(node.varId!, tNode.NUMBER);
      // allConstraints.push(["hasType", node.varId, NUMBER, `${node.text!} ∈ number`]);
    },
    StringKeyword(node) {
      if (node.varId === undefined) return;
      emit.allocPrimitive(node.varId!, tNode.STRING);
      // allConstraints.push(["hasType", node.varId, STRING, `${node.text!} ∈ string`]);
    },
    BooleanKeyword(node) {
      if (node.varId === undefined) return;
      emit.allocPrimitive(node.varId!, tNode.BOOLEAN);
      // allConstraints.push(["hasType", node.varId, BOOLEAN, `${node.text!} ∈ boolean`]);
    },
    VoidKeyword(node) {
      if (node.varId === undefined) return;
      emit.allocPrimitive(node.varId!, tNode.VOID);
      // allConstraints.push(["hasType", node.varId, VOID, `${node.text!} ∈ void`]);
    },
    AnyKeyword(node) {
      if (node.varId === undefined) return;
      emit.allocPrimitive(node.varId!, tNode.ANY);
      // allConstraints.push(["hasType", node.varId, ANY, `${node.text!} ∈ any`]);
    },
    UndefinedKeyword(node) {
      if (node.varId === undefined) return;
      emit.allocPrimitive(node.varId!, tNode.UNDEFINED);
      // allConstraints.push(["hasType", node.varId, UNDEFINED, `${node.text!} ∈ undefined`]);
    },
    // ObjectKeyword(node) {
    //   // 用法存疑
    //   if (node.varId === undefined) return;
    //   const id = newTypeNode({ kind: "object", name: "Object", id: node.varId!, properties: Object.create(null) });
    //   allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ Object`]);
    // },
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
        emit.flow(typeId, node.varId!, `this keyword`);
        // allConstraints.push(["sameID", node.varId!, typeId, `same identifier: ${node.text!}`]);
      }
      else {
        // varBindings.set(node.text, node.varId!);
        // console.warn(`Identifier ${node.text} not found in varBindings, using its own varId ${node.varId}`);
      }
    },
    // LiteralType(node) {
    //   if (node.varId === undefined) return;
    //   const id = newTypeNode({ kind: "primitive", name: node.text || "unknown LiteralType" });
    //   allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ ${node.text!}`]);
    // },
    // ArrayType(node) {
    //   if (node.children && node.children.length >= 3) {
    //     const elementTypeNode = node.children[0];
    //     if (elementTypeNode.varId !== undefined && node.varId !== undefined) {
    //       allConstraints.push(["makeArray", node.varId, elementTypeNode.varId, `${node.text!} ∈ ${elementTypeNode.text}[]`]);
    //       setTypeVar(node.varId!, newTypeNode({ kind: "array", elementType: UNKNOWN }) );
    //     }
    //   }
    // },
    // UnionType(node) {
    //   // UnionTypee : { SyntaxList : { keywd1 | keywd2 } } 
    //   if (node.children) {
    //     const n = node.children[0];
    //     if (n.children && n.children.length > 0) {
    //       const types: number[] = [];
    //       for (const child of n.children) {
    //         if (child.varId !== undefined && child.kind !== "BarToken") {
    //           allConstraints.push(["sameType", node.varId!, child.varId, `UnionType ${child.text!}`]);
    //         }
    //       }
    //     }
    //   }
    // },
    // PropType(node) {
    //   // if (node.children) {
    //   //   const types: number[] = [];
    //   //   for (const child of node.children[0].children || []) {
    //   //     if (child.varId !== undefined && child.varId in typeNodes) {
    //   //       types.push(child.varId);
    //   //     }
    //   //   }
    //   //   if (types.length > 0 && node.varId !== undefined) {
    //   //     const id = newTypeNode({ kind: "union", types });
    //   //     allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ ${types.map(printType).join(" | ")}`]);
    //   //   }
    //   // }
    // },
    // FunctionType(node) {
    //   // (param1: type1, param2: type2) => returnType
    //   // 清空param参数
    //   paramBindings.clear();
    //   // TODO
    // },
    // TypeReference(node) {
    //   // TODO
    //   if (node.children) {
    //     // const idNode = node.children[0];
    //     // if (idNode.varId !== undefined && idNode.text) {
    //     //   const typeId = varBindings.get(idNode.text);
    //     //   if (typeId !== undefined) {
    //     //     allConstraints.push(["sameID", node.varId!, typeId, `same Type: ${idNode.text!}`]);
    //     //   } else {
    //     //     // console.warn(`TypeReference ${idNode.text} not found in varBindings`);
    //     //   }
    //     // }
    //     const idNode = node.children[0];
    //     if (idNode.varId !== undefined) {
    //       allConstraints.push(["sameID", node.varId!, idNode.varId, `TypeReference ${idNode.text!}`]);
    //     }
    //   }
    // },
    // 赋予属性
    PropertyAssignment(node) {
      if (node.children?.length === 3) {
        // 清楚引号
        const idNode = node.children[0].kind === "StringLiteral" ? node.children[0].text?.slice(1, -1) : node.children[0].text;
        if (!idNode) return;
        meta.propName.set(node.varId!, idNode);
        meta.v8Kind.delete(node.children[2].varId!);
        // syntaxNodes[node.children[2].varId!].text = idNode; 
        // syntaxNodes[node.children[2].varId!].v8kind = undefined;
        const obj = node.parent?.parent;
        if (!obj || !obj.varId) return;
        emit.flow(node.children[2].varId!, node.varId!, `${node.text}`);
        emit.prop(obj.varId, node.varId!);
        // allConstraints.push(["initProperty", obj.varId, node.children[2].varId!, idNode!]);
      }
    },
    // 短赋予属性
    ShorthandPropertyAssignment(node) {
      if (node.children) {
        const obj = node.parent?.parent;
        if (!obj || !obj.varId) return;
        meta.propName.set(node.varId!, node.text!);
        meta.v8Kind.delete(node.children[0].varId!);
        emit.flow(node.children[0].varId!, node.varId!, `${node.text}`);
        emit.prop(obj.varId, node.varId!);
        // allConstraints.push(["initProperty", obj.varId, node.children[0].varId!, node.children[0].text!]);
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
            meta.propName.set(node.varId!, propName); 
            emit.prop(left.varId!, node.varId!);
            // allConstraints.push(["takeProperty", node.varId!, left.varId!, `${left.text!}.${propName}`]);
          }
        }
      }
    },
    TypeOfExpression(node) {
      if (node.children && node.children.length >= 2) {
        meta.v8Kind.set(node.varId!, "UnaryOperation");
        emit.unaryOp("typeof", node.children[1].varId!, node.varId!);
        // syntaxNodes[node.varId!].v8kind = "UnaryOperation";
        const operator = node.children[0]!;
        const operand = node.children[1]!;
        operator_cnts.set(operator.text!, (operator_cnts.get(operator.text!) || 0) + 1);
        operands.set(operator.text!, (operands.get(operator.text!) || new Set()).add(operand.varId!));
      }
    },
    VoidExpression(node) {
      meta.v8Kind.set(node.varId!, "UnaryOperation");
      emit.unaryOp("void", node.children?.[0].varId!, node.varId!);
      // syntaxNodes[node.varId!].v8kind = "UnaryOperation";
    },
    YieldExpression(node) {
      meta.v8Kind.set(node.varId!, node.children?.find(c => c.kind === "AsterisToken") ? "YieldStar" : "Yield");  
      // syntaxNodes[node.varId!].v8kind = node.children?.find(c => c.kind === "AsterisToken") ? "YieldStar" : "Yield";
    },
    // 处理一元操作
    PrefixUnaryExpression(node) {
      if (node.children && node.children.length >= 2) {
        const operator = node.children[0];
        const exprNode = node.children[1];
        meta.offset.set(node.varId!, operator.offset);
        meta.v8Kind.set(node.varId!, operator.text === "++" || operator.text === "--" ? "CountOperation" : "UnaryOperation");
        // syntaxNodes[node.varId!].offset = operator.offset;
        // syntaxNodes[node.varId!].v8kind = operator.text === "++" || operator.text === "--" ? "CountOperation" : "UnaryOperation";
        operator_cnts.set(operator.text!, (operator_cnts.get(operator.text!) || 0) + 1);
        operands.set(operator.text!, (operands.get(operator.text!) || new Set()).add(exprNode.varId!));
        emit.unaryOp(operator.text!, exprNode.varId!, node.varId!);
        // if (exprNode.varId !== undefined) {
        //   if (operator.kind === "ExclamationToken") {
        //     emit.allocPrimitive(node.varId!, BOOLEAN);
        //     // allConstraints.push(["hasType", node.varId!, BOOLEAN, `!${exprNode.text!} ∈ boolean`]);
        //     // allConstraints.push(["refersTo", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
        //   } else if (operator.kind === "PlusToken" || operator.kind === "MinusToken" || operator.kind === "TildeToken") {
        //     emit.allocPrimitive(node.varId!, NUMBER);
        //     // allConstraints.push(["sameType", node.varId!, exprNode.varId!, `-${exprNode.text!}`]);
        //     // allConstraints.push(["refersTo", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
        //   } else if (operator.kind === "PlusPlusToken" || operator.kind === "MinusMinusToken") {
        //     emit.allocPrimitive(node.varId!, NUMBER);
        //     emit.flow(node.varId!, exprNode.varId!, `${operator.text}${exprNode.text!}`);
        //   }
        // }
      }
      // TODO: 处理其他一元操作
    },
    PostfixUnaryExpression(node) {
      // syntaxNodes[node.varId!].v8kind = "CountOperation";
      const exprNode = node.children![0];
      const operator = node.children![1];
      meta.v8Kind.set(node.varId!, "CountOperation");
      meta.offset.set(node.varId!, operator.offset);
      // syntaxNodes[node.varId!].offset = operator.offset;
      operator_cnts.set(operator.text!, (operator_cnts.get(operator.text!) || 0) + 1);
      operands.set(operator.text!, (operands.get(operator.text!) || new Set()).add(exprNode.varId!));
      emit.unaryOp(operator.text!, exprNode.varId!, node.varId!);
      // emit.allocPrimitive(node.varId!, NUMBER);
      // emit.flow(node.varId!, exprNode.varId!, `${exprNode.text!}${operator.text}`);
    },
    // 二元操作
    BinaryExpression(node) {
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        if (!left.varId || !right.varId) return;
        if (meta.v8Kind.get(node.varId!) !== "NaryOperation") meta.offset.set(node.varId!, operator.offset);
        // if(syntaxNodes[node.varId!].v8kind !== "NaryOperation") syntaxNodes[node.varId!].offset = operator.offset;
        operator_cnts.set(operator.text!, (operator_cnts.get(operator.text!) || 0) + 1);
        operands.set(operator.text!, (operands.get(operator.text!) || new Set()).add(left.varId));
        operands.set(operator.text!, (operands.get(operator.text!) || new Set()).add(right.varId));
        emit.binaryOp(operator.text!, left.varId!, right.varId!, node.varId!);

        const compoundAssignmentOperators = ["FirstCompoundAssignment","MinusEqualsToken","AsteriskEqualsToken","SlashEqualsToken","PercentEqualsToken","AsteriskAsteriskEqualsToken","AmpersandEqualsToken","BarEqualsToken"];
        const arithmeticOperators = ["PlusToken","MinusToken","AsteriskToken","SlashToken","PercentToken","AsteriskAsteriskToken"];
        const logicalOperators = ["AmpersandAmpersandToken", "BarBarToken", "QuestionQuestionToken"];
        const comparisonOperators = ["LessThanToken","GreaterThanToken","LessThanEqualsToken","GreaterThanEqualsToken","EqualsEqualsToken","ExclamationEqualsToken","EqualsEqualsEqualsToken","ExclamationEqualsEqualsToken"];
        const bitwiseOperators = ["AmpersandToken","BarToken","CaretToken","TildeToken","LessThanLessThanToken","GreaterThanGreaterThanToken","GreaterThanGreaterThanGreaterThanToken"];

        // 处理赋值操作
        if (operator.kind === "FirstAssignment") {
          meta.v8Kind.set(node.varId!, "Assignment");
          meta.v8Kind.delete(left.varId!);
          // syntaxNodes[node.varId!].v8kind = "Assignment";
          // syntaxNodes[left.varId!].v8kind = undefined;
          // emit.flow(right.varId!, left.varId!, `${left.text!} = ${right.text!}`);
        }
        if (compoundAssignmentOperators.includes(operator.kind)) {
          meta.v8Kind.set(node.varId!, "CompoundAssignment");
          meta.v8Kind.delete(left.varId!);
          // syntaxNodes[node.varId!].v8kind = "CompoundAssignment";
          // syntaxNodes[left.varId!].v8kind = undefined;
          // emit.allocPrimitive(node.varId!, NUMBER);
          // emit.flow(node.varId!, left.varId!, `${left.text!} ${operator.text} ${right.text!}`);
          // allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} = ${right.text!}`]);
          // allConstraints.push(["sameType", node.varId!, right.varId, `${node.text!} = ${right.text!}`]);
          // // allConstraints.push(["sameType", right.varId!, left.varId, `${left.text!} = ${right.text!}`]);
          // // 处理对象属性设置
          // if (left.kind === "PropertyAccessExpression" && left.children && left.children.length! >= 3) {
          //   syntaxNodes[node.varId!].v8kind = undefined;
          //   allConstraints.push(["setProperty", left.children[0].varId!, left.varId, `${left.children[0].text}.${left.children[2].text} = ${right.text}`]);
          // } else if (left.kind === "ElementAccessExpression" && left.children && left.children.length! >= 4) {
          //   syntaxNodes[node.varId!].v8kind = undefined;
          //   allConstraints.push(["setElement", left.children[0].varId!, left.varId, `${left.children[0].text}[${left.children[2].text}] = ${right.text}`]);
          // }
        }
        // 处理加减乘除模运算
        else if (arithmeticOperators.includes(operator.kind)) {
          // allConstraints.push(["sameType", left.varId!, right.varId!, `${left.text!} == ${right.text!}`]);
          meta.v8Kind.set(node.varId!, "BinaryOperation");
          // syntaxNodes[node.varId!].v8kind ??= "BinaryOperation";
          if (node.parent?.kind === "BinaryExpression" && node.parent.children?.[1].kind === operator.kind) {
            meta.v8Kind.set(node.parent.varId!, "NaryOperation");
            meta.offset.set(node.parent.varId!, node.parent.offset);
            meta.v8Kind.set(node.varId!, "invisible");
            // syntaxNodes[node.parent.varId!].v8kind = "NaryOperation";
            // syntaxNodes[node.parent.varId!].offset = node.parent.offset;
            // syntaxNodes[node.varId!].v8kind = "invisible";
          }
          // allConstraints.push(["sameType", node.varId!, right.varId!, `${node.text!} = ${right.text!}`]);
          // allConstraints.push(["sameType", node.varId!, left.varId!, `${node.text!} == ${left.text!}`]);
        }
        // 处理逻辑运算
        else if (logicalOperators.includes(operator.kind)) {
          meta.v8Kind.set(node.varId!, "BinaryOperation");
          // syntaxNodes[node.varId!].v8kind ??= "BinaryOperation";
          if (node.parent?.kind === "BinaryExpression" && node.parent.children?.[1].kind === operator.kind) {
            meta.v8Kind.set(node.parent.varId!, "NaryOperation");
            meta.offset.set(node.parent.varId!, node.parent.offset);
            meta.v8Kind.set(node.varId!, "invisible");
            // //  
            // syntaxNodes[node.parent.varId!].v8kind = "NaryOperation";
            // syntaxNodes[node.parent.varId!].offset = node.parent.offset;
            // syntaxNodes[node.varId!].v8kind = "invisible";
          }
          // allConstraints.push(["sameType", node.varId!, left.varId!, `${node.text!} = ${left.text!}`]);
          // allConstraints.push(["sameType", node.varId!, right.varId!, `${node.text!} = ${right.text!}`]);
        }
        // 处理比较运算
        else if (comparisonOperators.includes(operator.kind)) {
          // allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
          meta.v8Kind.set(node.varId!, "CompareOperation");
          // syntaxNodes[node.varId!].v8kind = "CompareOperation";
          // 认为是同一类型
          // allConstraints.push(["sameType", left.varId, right.varId, `${left.text!} ${operator.text} ${right.text}`]);
          // allConstraints.push(["sameType", right.varId, left.varId, `${left.text!} ${operator.text} ${right.text}`]);
        }
        // 处理位运算
        else if (bitwiseOperators.includes(operator.kind)) {
          meta.v8Kind.set(node.varId!, "BinaryOperation");
          // syntaxNodes[node.varId!].v8kind ??= "BinaryOperation";
          if (node.parent?.kind === "BinaryExpression" && node.parent.children?.[1].kind === operator.kind) {
            meta.v8Kind.set(node.parent.varId!, "NaryOperation");
            meta.offset.set(node.parent.varId!, node.parent.offset);
            meta.v8Kind.set(node.varId!, "invisible");
            // //
            // syntaxNodes[node.parent.varId!].v8kind = "NaryOperation";
            // syntaxNodes[node.parent.varId!].offset = node.parent.offset;
            // syntaxNodes[node.varId!].v8kind = "invisible";
          }
          // allConstraints.push(["hasType", node.varId!, NUMBER, `${left.text} ${operator.text} ${right.text}`]);
        }
        // instance of
        else if (operator.kind === "InstanceOfKeyword") { 
          meta.v8Kind.set(node.varId!, "BinaryOperation");
          // syntaxNodes[node.varId!].v8kind ??= "BinaryOperation";
          // let parent = node.parent;
          // while (parent && parent?.kind !== "FunctionDeclaration") parent = parent.parent;
          // // trick
          // if (parent && parent.kind === "FunctionDeclaration" && parent.children?.[1].text === "_classCallCheck") {
          //   allConstraints.push(["hasType", node.varId!, newTypeNode({ kind: "literal", value: true}), `${node.text!} ∈ true`]);
          // } else allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
        }
        // TODO: 更多二元运算
      }
    },
    // 处理数组字面量
    ElementAccessExpression(node) {
      meta.v8Kind.set(node.varId!, "Property");
      // syntaxNodes[node.varId!].v8kind = "Property"
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const right = node.children[2];
        meta.offset.set(node.varId!, node.children[1].offset);  
        // syntaxNodes[node.varId!].offset = node.children[1].offset;
        if (left.varId !== undefined && node.varId !== undefined) {
          emit.arrayElement(left.varId!, node.varId!);
          // allConstraints.push(["elementAccess", node.varId, left.varId, `${left.text!}[${right.text!}]`]);
        }
      }
    },
    // 处理属性访问
    PropertyAccessExpression(node) {
      meta.v8Kind.set(node.varId!, "Property");
      // syntaxNodes[node.varId!].v8kind = "Property"
      if (node.children && node.children.length >= 3) {
        const left = node.children[0];
        const operator = node.children[1];
        const right = node.children[2];
        meta.offset.set(node.varId!, right.offset);
        meta.v8Kind.delete(right.varId!);
        // syntaxNodes[node.varId!].offset = right.offset;
        // syntaxNodes[right.varId!].v8kind = undefined;
        // 处理dot运算符
        if ((operator.kind === "DotToken" || operator.kind === "QuestionDotToken") && left.varId !== undefined && right.varId !== undefined) {
          // 处理属性访问
          const propName = right.text;
          if (propName) {
            meta.propName.set(node.varId!, propName);
            emit.prop(left.varId!, node.varId!);
            // allConstraints.push(["takeProperty", node.varId!, left.varId!, `${left.text!}.${propName}`]);
          }
        }
      }
    },
    // New运算符
    NewExpression(node) {
      meta.v8Kind.set(node.varId!, "CallNew");  
      // syntaxNodes[node.varId!].v8kind = "CallNew"
      if (node.children) {
        const classNode = node.children.find(n => n.kind === "Identifier");
        if (classNode?.varId !== undefined) {
          emit.newinstance(classNode.varId!, node.varId!);
          // allConstraints.push(["sameType", node.varId!, classNode.varId, `new ${classNode.text!}`]);

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
              emit.arg(constr, arg.varId!, idx);
              // allConstraints.push(["funcToArg", arg.varId!, constr * 1000 + idx, `${node.text}`]);
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
          emit.flow(exprNode.varId!, node.varId!, `(${exprNode.text!})`);
          // allConstraints.push(["sameType", node.varId!, exprNode.varId!, `(${exprNode.text!})`]);
        }
      }
    },
    // 处理非空断言: x!
    NoneNullExpression(node) {
      if (node.children && node.children.length >= 2) {
        const exprNode = node.children[0];
        if (exprNode.varId !== undefined) {
          emit.flow(exprNode.varId!, node.varId!, `${exprNode.text!}!`);
          // allConstraints.push(["sameType", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
        }
      }
    },
    // 处理标识符
    Identifier(node) {
      if (tsMorphNodes.includes(node.parent?.kind!)) meta.v8Kind.set(node.varId!, "VariableProxy"); // syntaxNodes[node.varId!].v8kind = "VariableProxy";
      if (node.text) {
        if (node.text === "undefined") {
          emit.allocPrimitive(node.varId!, UNDEFINED);
          // allConstraints.push(["hasType", node.varId!, UNDEFINED, `${node.text!} ∈ undefined`]);
          return;
        }
        const typeId = paramBindings.get(node.text) ?? varBindings.get(node.text);

        if (typeId !== undefined) {
          if (node.parent?.kind === "PropertyAssignment" && node.parent?.children?.[2] === node) {
            // 属性赋值时不添加sameID约束
            emit.flow(typeId, node.varId!, `property assignment for ${node.text!}`);
            // allConstraints.push(["sameType", node.varId!, typeId, `same identifier: ${node.text!}`]);
            // allConstraints.push(["sameType", typeId, node.varId!, `same identifier: ${node.text!}`]);
          } else {
            emit.sameID(node.varId!, typeId);
            // allConstraints.push(["sameID", node.varId!, typeId, `same identifier: ${node.text!}`]);
            if (typeId === node.varId) {
              const makeup = unprocsdVars.get(node.text);
              for (const mu of makeup || []) {
                emit.sameID(mu, typeId);
                // allConstraints.push(["sameID", mu, node.varId!, `same identifier by makeup: ${node.text!}`]);
              }
            }
          }
        } else {
          unprocsdVars.set(node.text, (unprocsdVars.get(node.text) || new Set()).add(node.varId!));
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
      meta.v8Kind.set(node.varId!, "Conditional");
      // syntaxNodes[node.varId!].v8kind = "Conditional";
      if (node.children && node.children.length >= 5) {
        const condition = node.children[0];
        const trueBranch = node.children[2];
        const falseBranch = node.children[4];
        if (condition.varId !== undefined && trueBranch.varId !== undefined && falseBranch.varId !== undefined) {
          emit.ternaryOp(condition.varId!, trueBranch.varId!, falseBranch.varId!, node.varId!);
          // allConstraints.push(["sameType", node.varId!, trueBranch.varId!, `? ${trueBranch.text!} : ${falseBranch.text!}`]);
          // allConstraints.push(["sameType", node.varId!, falseBranch.varId!, `? ${trueBranch.text!} : ${falseBranch.text!}`]);
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
        // funcNode = funcNode?.kind === "ArrowFunction" || funcNode?.kind === "FunctionExpression" ? funcNode : funcNode?.children?.find(n => n.kind === "Identifier");

        if (!funcNode || !funcNode.varId || !exprNode.varId) return;
        if (exprNode.kind === "SemicolonToken") {
          emit.returnVoid(funcNode.varId!);
          // allConstraints.push(["hasType", node.varId!, VOID, "return; ∈ VOID"]);
          // allConstraints.push(["returnType", node.varId!, node.varId!, `return;`]);
        } else {
          emit.returnStmt(funcNode.varId!, exprNode.varId!);
        }
          // allConstraints.push(["returnType", funcNode.varId!, exprNode.varId!, `return value of function ${funcNode.text!}`]);
      }
    },
    // 处理函数调用
    CallExpression(node) {
      meta.v8Kind.set(node.varId!, "Call");
      // syntaxNodes[node.varId!].v8kind = "Call";
      if (node.children && node.children.length >= 2) {
        // 不能改为在bindings中查找，因为有可能是匿名函数调用
        const funcNode = node.children[0];
        if (funcNode.varId !== undefined && node.varId !== undefined) {
          meta.offset.set(node.varId!, funcNode.kind === "PropertyAccessExpression" ? funcNode.children?.[2]?.offset! : funcNode.offset);
          // syntaxNodes[node.varId!].offset = funcNode.kind === "PropertyAccessExpression" ? funcNode.children?.[2]?.offset : funcNode.offset;
          emit.call(funcNode.varId!, node.varId!);
          // allConstraints.push(["funcCall", node.varId, funcNode.varId, `${node.text}`]);

          // 处理实参
          const args = node.children.find(n => n.kind === "SyntaxList");
          let idx = 0;
          // 使用varBindings中的varId（如果存在），以便正确解析函数绑定
          let funcVarId = funcNode.varId!;
          if (funcNode.kind === "Identifier" && varBindings.has(funcNode.text!)) {
            funcVarId = varBindings.get(funcNode.text!)!;
          }
          for (const arg of args?.children?.filter(n => n.kind !== "CommaToken") ?? []) {
            emit.arg(funcVarId, arg.varId!, idx);
            // allConstraints.push(["funcToArg", arg.varId!, funcNode.varId * 1000 + idx, `${node.text}`]);
            idx++;
          }
        }
      }
    },
    // 处理箭头函数 () => {}
    ArrowFunction(node) {
      // 如果没有block，退出作用域，必须postOrder!
      meta.v8Kind.set(node.varId!, "FunctionLiteral");
      // syntaxNodes[node.varId!].v8kind = "FunctionLiteral";
      if (!node.children?.some(n => n.kind === "Block")) {
        const previous = scopeStack.pop();
        unprocsdScopes.pop();
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
          console.error("Scope stack underflow: too many closing braces");
        }
      }
      // TODO: 其余操作
      if (node.children) {
        emit.allocFunction(node.varId!, node.varId!);
        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            emit.returnAnnot(node.varId!, typeNode.varId!);
            // const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: node.varId!, params: [], returnType: UNKNOWN });
            // setTypeVar(node.varId!, id);
            // allConstraints.push(["returnAnnotation", node?.varId!, typeNode.varId, `return type of function ${node?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          emit.returnVoid(node.varId!);
          // const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: node?.varId!, params: [], returnType: VOID });
          // setTypeVar(node.varId!, id);
        }
        // else {
        //   const id = newTypeNode({ kind: "function", name: `anonymous${node.varId}`, id: node?.varId!, params: [], returnType: UNKNOWN });
        //   setTypeVar(node.varId!, id);
        // }
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
        unprocsdScopes.push(unprocsdVars);
        unprocsdVars = new Map();
        // 加入parameter绑定
        for (const [name, id] of paramBindings.entries()) {
          varBindings.set(name, id);
        }
        // 清空paramBindings
        paramBindings.clear();
      }
    },
    // 处理类型断言和as表达式
    AsExpression(node) {
      if (node.children && node.children.length >= 3) {
        const exprNode = node.children[0];
        const asExprNode = node.children[2];
        if (exprNode.varId !== undefined && node.varId !== undefined && asExprNode.text) {
          emit.flow(exprNode.varId!, asExprNode.varId!, `${exprNode.text!} as ${asExprNode.text!}`);
        }
        // TODO: 添加类型断言约束
        const typeNode = node.children[2];
      }
    },
    // 处理作用域{
    FirstPunctuation(node) {
      scopeStack.push(varBindings);
      varBindings = new Map(varBindings);
      unprocsdScopes.push(unprocsdVars);
      unprocsdVars = new Map();
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
      unprocsdScopes.pop();
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
        console.error("Scope stack underflow: too many closing braces");
      }
    }
  }



  function walk(node: AstNode) {
    const id = node.varId;
    if (id === undefined) throw new Error("Missing varId in second pass");
    meta.file.set(id, filePath);
    meta.pos.set(id, node.position);
    meta.offset.set(id, node.offset);
    meta.kind.set(id, node.kind);
    if (node.text) {
      meta.text.set(id, node.text);
      meta.context.set(id, node.parent?.text ?? node.text)
    }
    // syntaxNodes[id] = { kind: node.kind, text: node.text, file: filePath, position: node.position, offset: node.offset, context: node.parent?.text 
// };
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

// // 输出图和约束
// function emitGlobalTypeGraphAndConstraints() {
//   const types = deriveVariableTypes();
//   if(LOG_EVALUATE_STCS) evaluate();

//   const outDir = path.join(outputDir, "typegraph");
//   fs.mkdirSync(outDir, { recursive: true });

//   // 写出 constraints 和推理类型
//   const constraintOut = path.join(outDir, "constraints.json");
//   writeJsonStream(constraintOut, { allConstraints, types });

//   // 写出类型图（仅 JSON）
//   const jsonGraph = generateTypeGraphJson();
//   const jsonOut = path.join(outDir, "typegraph.json");
//   writeJsonStream(jsonOut, jsonGraph);

//   // 写出类型标注结果
//   const json = generateTypeAnno();
//   const outfile = path.join(outputDir, "typeinfo.json");
//   writeJsonStream(outfile, json);

//   // 按 file 分组
//   const groups : Record<string, any> = {};
//   for (const item of json) {
//     if (!groups[item.relapath]) groups[item.relapath] = [];
//     const { file, relapath, ...rest } = item;  // 去掉 file 字段
//     groups[item.relapath].push(rest);
//   }

//   for (const file in groups) {
//     const outfile = path.join(path.join(outputDir, "typeinfo"), file + ".json");
//     fs.mkdirSync(path.dirname(outfile), { recursive: true }); // 创建目录
//     writeJsonStream(outfile, groups[file]);
//   }

//   console.log(`Done. Output written to ${outDir}`);

//   // ===== JSON 图生成函数 =====
//   function generateTypeGraphJson(): { nodes: any[]; edges: any[] } {
//     const nodes: any[] = [];
//     const edges: any[] = [];
//     const seen = new Set<number>();

//     for (const [srcId, dsts] of graph) {
//       const srcVar = syntaxNodes[srcId];
//       const srcfile = syntaxNodes[srcId]?.file || "unknown";
//       if (!seen.has(srcId)) {
//         nodes.push({
//           id: srcId,
//           label: srcVar?.text || `var_${srcId}`,
//           typeid: typeSet.get(srcId) ?? UNKNOWN,
//           type: printType(typeSet.get(srcId) ?? UNKNOWN),
//           fullType: printFullType(typeSet.get(srcId) ?? UNKNOWN),
//           jsonType: printJsonType(typeSet.get(srcId) ?? UNKNOWN),
//           text: srcVar?.text,
//           file: srcfile.replace(".ast.json", "").replace(/\^/g, "\/").split("ast\/")[1],
//           position: srcVar?.position,
//         });
//         seen.add(srcId);
//       }

//       for (const [dstId, edgeKind] of dsts) {
//         const dstVar = syntaxNodes[dstId];
//         const dstfile = syntaxNodes[dstId]?.file || "unknown";
//         if (!seen.has(dstId)) {
//           nodes.push({
//             id: dstId,
//             label: dstVar?.text || `var_${dstId}`,
//             typeid: typeSet.get(dstId) ?? UNKNOWN,
//             type: printType(typeSet.get(dstId) ?? UNKNOWN),
//             fullType: printFullType(typeSet.get(dstId) ?? UNKNOWN),
//             jsonType: printJsonType(typeSet.get(dstId) ?? UNKNOWN),
//             text: dstVar?.text,
//             file: dstfile.replace(".ast.json", "").replace(/\^/g, "\/").split("ast\/")[1],
//             position: dstVar?.position,
//           });
//           seen.add(dstId);
//         }

//         edges.push({ from: srcId, to: dstId, label: edgeKind });
//       }
//     }

//     return { nodes, edges };
//   }

function main() {

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


  solver.solve(fact);
  solver.output();
}

// // 递归获取所有 AST 文件
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

export {tNode, solver, outputDir, meta};