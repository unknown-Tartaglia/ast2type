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

const LOG_SCOPE = false; // 是否开启日志作用域
const LOG_TYPENODE = false; // 是否开启类型节点日志
const LOG_TYPENODE_VERBOSE = false; // 是否开启类型节点详细日志
const LOG_IDENTIFIER_NODE = false; // 是否开启标识符节点日志
const LOG_IMPORT = false; // 是否开启导入日志
const LOG_TYPE_FLOW = false; // 是否开启类型流日志

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
  | { kind: "function"; params: Param[]; returnType: number }
  | { kind: "union"; types: number[] }
  | { kind: "object"; name: string; properties: Record<string, number> }
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
}

// 全局结构
let typeVarCounter = 100;
const cnt: Record<number, number> = {};
const fileToAst: Record<string, AstNode> = {};
const globalExportMap: Record<string, Record<string, number>> = {};
const syntaxNodes: Record<number, { kind: string; text?: string; file?: string; position?: any }> = {};
const typeNodes: Record<number, TypeNode> = {};
const allConstraints: Array<[string, number, number, string]> = [];
const globalVarBindings = new Map<string, number>();
const func2typeId = new Map<string, number>();
const universe = new Set<string>();
const graph: Record<number, Record<number, string>> = {};
const source: Record<number, Record<number, number>> = {};
const typeSet: Record<number, number> = {};
const del: Record<number, Set<number>> = {};
const parent: Record<number, number> = {};
const globalImportMap : Map<string, string> = new Map(JSON.parse(fs.readFileSync(path.join(inputDir, "importMap.json"), "utf8")));
let worklist: number[] = [];

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
    const t = typeNodes[n];
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
        const paramsStr = t.params.map(p => `${p.name}: ${helper(p.type)}`).join(", ");
        return `(${paramsStr}) => ${helper(t.returnType)}`;
      case "object":
        return `object:${t.name}`;
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
    const t = typeNodes[n];
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
        const paramsStr = t.params.map(p => `${p.name}: ${helper(p.type)}`).join(", ");
        return `(${paramsStr}) => ${helper(t.returnType)}`;
      case "object":
        if (occur[t.name]) {
          return `object:${t.name}`;
        }
        occur[t.name] = n;
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
function serializeTypeNode(t: TypeNode): string {
  if (!t) {
    // if (LOG_TYPENODE)
      console.warn(`illegal typeNode ${JSON.stringify(t)}`);
    return "illegal typeNode";
  }
  switch (t.kind) {
    case "primitive":
      return `primitive:${t.name}`;
    case "array":
      return `array:${t.elementType}`;
    case "function":
      return `function:${t.params.map(p => `${p.name}:${p.type}`).join(",")}->${t.returnType}`;
    case "union":
      return `union:${t.types.sort().join("|")}`;
    case "object":
      return `object:{${t.name}:${Object.entries(t.properties).sort().map(([k, v]) => `${k}:${v}`).join(",")}}`;
    case "enum":
      return `enum:{${t.name}:${Object.entries(t.members).sort().map(([k, v]) => `${k}=${v}`).join(",")}}`;
  }
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
  const occur: Record<string, number> = {};
  return helper(ty);
  function helper(t: TypeNode): number {
    if (!t) {
      // if (LOG_TYPENODE)
        console.warn(`Undefined typeNode in newTypeNode`);
      return UNKNOWN; // 返回UNKNOWN
    }
    if (t.kind === "array") {
      const ret = helper(typeNodes[t.elementType]);
      if (t.elementType !== ret) {
        t.elementType = ret;
      }
    }
    else if (t.kind === "function") {
      for (const param of t.params) {
        const ret = helper(typeNodes[param.type]);
        if (param.type !== ret) {
          param.type = ret;
        }
      }
      const returnType = helper(typeNodes[t.returnType]);
      if (t.returnType !== returnType) {
        t.returnType = returnType;
      }
    } else if (t.kind === "union") {
      const newTypes = t.types.map(ty => helper(typeNodes[ty]));
      t.types = newTypes;
    } else if (t.kind === "object") {
      // console.log(`enter ${t.name}`)
      if (occur[t.name]) {
        occur[t.name] = newTypeNode(t)
        return occur[t.name];
      }
      occur[t.name] = UNKNOWN;
      for (const key in t.properties) {
        const ret = helper(typeNodes[t.properties[key]]);
        if (t.properties[key] !== ret) {
          t.properties[key] = ret;
        }
      }
      if (occur[t.name] !== UNKNOWN && serializeTypeNode(typeNodes[occur[t.name]]) !== serializeTypeNode(t)) {
        // 修改TypeNode，危险操作，传播影响
        if (LOG_TYPENODE) {
          console.log(`Change type node ${occur[t.name]} from ${JSON.stringify(typeNodes[occur[t.name]]) } to ${JSON.stringify(t)}`);
        }
        typeNodes[occur[t.name]] = t;
        typeNodeReverseMap.set(serializeTypeNode(t), occur[t.name]);
        for (const idStr in typeSet)
          if (typeSet[Number(idStr)] === occur[t.name])
            worklist.push(Number(idStr));
        return occur[t.name];
      }
      // console.log(`exit ${t.name}`)
    }
    serialized = serializeTypeNode(t);
    if (typeNodeReverseMap.has(serialized)) {
      const id = typeNodeReverseMap.get(serialized)!;
      return id;
    } else {
      const id = typeVarCounter++;
      typeNodes[id] = t;
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
    if (typeNodes[ty].kind === "union") 
      tyList = tyList.concat([...typeNodes[ty].types]);
    else tyList.push(ty);
  }
  

  tyList = [...new Set(tyList.filter(ty => ty !== UNKNOWN))];


  if (tyList.length === 1) {
    ret = tyList[0];
  } else if (tyList.length > 1) {
    ret = newTypeNode( { kind: "union", types: tyList});
  } else {
    console.warn(`Trap!!! merge types ${[...tys]} to UNKNOWN`);
    ret = UNKNOWN;
  }
  if (LOG_TYPE_FLOW) 
    console.log(`merge types ${[...tys]} to ${ret}`);
  return ret;
}

// 合并不同分支类型
function mergeBranches(node : number, kinds? : string[]) : number {
  let ret : number;
  if (Object.keys(source[node]).length === 1) {
    const src = Number(Object.keys(source[node])[0]);
    if (kinds && !kinds.includes(graph[src][node])) {
      console.warn(`Unexpected merge branches when branchNum = 1 && edge ${src}->${node} not in type ${[...kinds]}`);
    }
    ret = source[node][src];
  }
  else {
    let tyList : number[] = [];
    for (const srcStr in source[node]) {
      const src = Number(srcStr);
      if (kinds && !kinds.includes(graph[src][node])) continue;
      const ty = source[node][src];
      if (typeNodes[ty].kind === "union") 
        tyList = tyList.concat([...typeNodes[ty].types]);
      else tyList.push(ty);
    }

    
    tyList = [...new Set(tyList.filter(ty => ty !== UNKNOWN))];


    if (tyList.length === 1) {
      ret = tyList[0];
    } else if (tyList.length > 1) {
      ret = newTypeNode( { kind: "union", types: tyList});
    } else {
      ret = UNKNOWN;
    }
  }
  if (LOG_TYPE_FLOW) 
    console.log(`merge branches at ${node} from ${[...Object.values(source[node]) ]} to ${ret} as ${serializeTypeNode(typeNodes[ret])}`)
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
    for (const child of node.children || []) {
      child.parent = node;
      walk(child);
    }

    // 还原filepath中的^为\\
    let realPath = path.basename(filePath).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");

    // export Class Enum TypeAlias
    if ((node.kind === "ClassDeclaration" || node.kind === "EnumDeclaration" || node.kind === "TypeAliasDeclaration") && findNodesByKind(node, "ExportKeyword").length > 0) {
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

    // exportDeclararion
    if (node.kind === "ExportDeclaration" || node.kind === "ExportAssignment") {
      const idNodes = findNodesByKind(node, "Identifier");
      for (const idNode of idNodes) 
        if (idNode && idNode.text) {
          globalExportMap[realPath] ??= {};
          globalExportMap[realPath][idNode.text] = idNode.varId!;
          
          // 处理default
          const dftkwd = findNodesByKind(node, "DefaultKeyword")[0];
          if (dftkwd) {
            globalExportMap[realPath][dftkwd.text!] = dftkwd.varId!;
            allConstraints.push(["sameType", dftkwd.varId!, idNode.varId!, "default keyword"]);
            // TODO: 判断是否只有一个default
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
            const id = newTypeNode({ kind: "function", params: [], returnType: UNKNOWN });
            typeSet[idNode?.varId!] = id;
            allConstraints.push(["returnAnnotation", idNode?.varId!, typeNode.varId, `return type of function ${idNode?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          const id = newTypeNode({ kind: "function", params: [], returnType: VOID });
          typeSet[idNode?.varId!] = id;
        }
        else {
          const id = newTypeNode({ kind: "function", params: [], returnType: UNKNOWN });
          typeSet[idNode?.varId!] = id;
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
      allConstraints.push(["setProperty", paNode.varId!, left.varId!, `${paNode.text!}.${left.text!}`]);
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

        let funcIdNode = node.parent;
        while (funcIdNode && funcIdNode.kind !== "FunctionDeclaration" && funcIdNode.kind !== "MethodDeclaration") funcIdNode = funcIdNode.parent;
        funcIdNode = funcIdNode?.children?.find(n => n.kind === "Identifier");
        if (!funcIdNode || !funcIdNode.varId) return;

        allConstraints.push(["setPramType", funcIdNode.varId!, paramIdNode.varId!, `parameter ${paramIdNode.text!} in function ${funcIdNode.text!}`]);
      }
    },
    // 处理枚举声明
    EnumDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId !== undefined) {
          const typeId = newTypeNode({ kind: "enum", name: idNode.text!, members: {} });
          typeSet[idNode.varId] = typeId;
          varBindings.set(idNode.text!, idNode.varId!);
        }

        //处理namespace
        let paNode = node.parent?.parent?.parent;
        if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
        paNode = paNode.children?.find(n => n.kind === "Identifier");
        if (!paNode) return;
        allConstraints.push(["setProperty", paNode.varId!, idNode.varId!, `${paNode.text!}.${idNode.text!}`]);
      }
    },
    // 处理枚举成员
    EnumMember(node) {
      const idNode = node.children?.find(n => n.kind === "Identifier");
      const paNode = findParentByKind(node, "EnumDeclaration")?.children?.find(n => n.kind === "Identifier");
      const nb = node.children?.find(n => n.kind === "FirstLiteralToken");
      if(!paNode || !paNode.varId || !idNode || !idNode || !nb?.text) return;
      varBindings.set(idNode.text!, idNode.varId!);

      const oldTypeId = typeSet[paNode.varId];
      if (!oldTypeId) return;
      const oldTypeNode = typeNodes[oldTypeId];
      if (!oldTypeNode || oldTypeNode.kind !== "enum") return;
      const newMembers = { ...oldTypeNode.members };
      newMembers[idNode.text!] = newTypeNode({ kind: "primitive", name: nb.text});

      const typeId = newTypeNode({ kind: "enum", name: idNode.text!, members: newMembers });
      typeSet[paNode.varId] = typeId;
    },
    // 处理接口声明
    InterfaceDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId !== undefined) {
          const typeId = newTypeNode({ kind: "object", name: idNode.text!, properties: Object.create(null) });
          typeSet[idNode.varId] = typeId;
          varBindings.set(idNode.text!, idNode.varId!);
        }

        //处理namespace
        let paNode = node.parent?.parent?.parent;
        if (!paNode || paNode.varId === undefined || paNode.kind !== "ModuleDeclaration") return;
        paNode = paNode.children?.find(n => n.kind === "Identifier");
        if (!paNode) return;
        allConstraints.push(["setProperty", paNode.varId!, idNode.varId!, `${paNode.text!}.${idNode.text!}`]);
      }
    },
    // 处理接口Property
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
            allConstraints.push(["setProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
            allConstraints.push(["annotation", propIdNode.varId, typeNode.varId, `annotation ${idNode.text!}.${propIdNode.text!} : ${typeNode.text!}`]);
          }
        } else {
          allConstraints.push(["setProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
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

        let funcType: TypeNode = { kind: "function", params: [], returnType: UNKNOWN };
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
        typeSet[methodIdNode.varId] = typeId;

        allConstraints.push(["setProperty", idNode.varId, methodIdNode.varId, `${methodIdNode.text!}() => ${printType(typeId)}`]);
      }
    },
    // 处理class声明
    ClassDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId) {
          const typeId = newTypeNode({ kind: "object", name: idNode.text!, properties: Object.create(null) });
          if (LOG_IDENTIFIER_NODE)
            console.log(`Class ${idNode.text} has type ID ${typeId}`);
          typeSet[idNode.varId] = typeId;
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

        allConstraints.push(["setProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);

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
        while (idNode && idNode.kind !== "ClassDeclaration") idNode = idNode.parent;
        idNode = idNode?.children?.find(n => n.kind === "Identifier");
        if (!idNode || idNode.varId === undefined) return;

        const propIdNode = node.children?.find(n => n.kind === "Identifier");
        if (propIdNode && propIdNode.varId !== undefined) {

          let funcType: TypeNode = { kind: "function", params: [], returnType: UNKNOWN };
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
          typeSet[propIdNode.varId] = typeId;

          allConstraints.push(["setProperty", idNode.varId, propIdNode.varId, `${propIdNode.text!}() => ${printType(typeId)}`]);
        }
      }
    },
    // 处理模块声明
    ModuleDeclaration(node) {
      const idNode = node.children?.find(n => n.kind === "Identifier");

      if(idNode && idNode.varId) {
        const typeId = newTypeNode({ kind: "object", name: idNode.text!, properties: Object.create(null) });
        typeSet[idNode.varId] = typeId;
        varBindings.set(idNode.text!, idNode.varId!);
      }
    },
    // 处理import声明
    ImportDeclaration(node) {
      const imported: AstNode[] = findNodesByKind(node, "Identifier");

      const raw = node.children?.find(n => n.kind === "StringLiteral")?.text;
      const moduleSpecifier = raw?.replace(/^['"]|['"]$/g, "");  // 去掉引号
      if (!moduleSpecifier) {
        if (LOG_IMPORT)
          console.warn(`ImportDeclaration in ${filePath} has no moduleSpecifier`);
        return;
      }

      const resolvedFile = resolveImportPath(filePath, moduleSpecifier);
      for (const idNode of imported) {
        const symbol = idNode.text!;
        varBindings.set(symbol, idNode.varId!);
        if (!resolvedFile) {
          if (LOG_IMPORT)
            console.warn(`can not resolve import ${moduleSpecifier} in ${filePath}`);
          allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
          continue;
        }

        const nsimpt = findNodesByKind(node, "NamespaceImport")[0];
        if (idNode.varId === nsimpt?.children?.find(n => n.kind === "Identifier")?.varId) {
          const typeId = newTypeNode({ kind: "object", name: idNode.text!, properties: Object.create(null) });
          typeSet[idNode.varId!] = typeId;
          varBindings.set(idNode.text!, idNode.varId!);
          for (const symb in globalExportMap[resolvedFile]) {
            allConstraints.push(["setProperty", idNode.varId!, globalExportMap[resolvedFile]?.[symb], ""])
          }
          continue;
        }

        const target = globalExportMap[resolvedFile]?.[symbol];
        if (target !== undefined) {
          allConstraints.push(["sameType", idNode.varId!, target, `import ${symbol} from ${moduleSpecifier}`]);
        } else {
          if (LOG_IMPORT)
            console.warn(`Symbol ${symbol} not found in export map of ${resolvedFile} in ${filePath}`);
          allConstraints.push(["sameType", idNode.varId!, 0, `Failed import ${symbol} from ${moduleSpecifier}`]);
        }
      }
    }
  }

  const handlers: Record<string, (node: AstNode) => void> = {
    StringLiteral(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
    },
    NoSubstitutionTemplateLiteral(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
    },
    FirstLiteralToken(node) {
      // 暂时默认为数字
      allConstraints.push(["hasType", node.varId!, NUMBER, `${node.text!} ∈ number`]);
    },
    NumericLiteral(node) {
      allConstraints.push(["hasType", node.varId!, NUMBER, `${node.text!} ∈ number`]);
    },
    TrueKeyword(node) {
      allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
    },
    FalseKeyword(node) {
      allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
    },
    NullKeyword(node) {
      allConstraints.push(["hasType", node.varId!, NULL, `${node.text!} ∈ null`]);
    },
    BigIntLiteral(node) {
      allConstraints.push(["hasType", node.varId!, NUMBER, `${node.text!} ∈ number`]);
    },
    RegularExpressionLiteral(node) {
      allConstraints.push(["hasType", node.varId!, REGEXP, `${node.text!} ∈ RegExp`]);
    },
    TemplateExpression(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
    },
    FirstTemplateToken(node) {
      allConstraints.push(["hasType", node.varId!, STRING, `${node.text!} ∈ string`]);
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
      const id = newTypeNode({ kind: "object", name: "Object", properties: Object.create(null) });
      allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ Object`]);
    },
    ThisKeyword(node) {
      if (node.varId === undefined) return;
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

    // 处理一元操作
    PrefixUnaryExpression(node) {
      if (node.children && node.children.length >= 2) {
        const operator = node.children[0];
        const exprNode = node.children[1];
        if (exprNode.varId !== undefined) {
          if (operator.kind === "ExclamationToken") {
            allConstraints.push(["hasType", node.varId!, BOOLEAN, `!${exprNode.text!} ∈ boolean`]);
            allConstraints.push(["refersTo", node.varId!, exprNode.varId!, `!${exprNode.text!}`]);
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
          allConstraints.push(["hasType", node.varId!, BOOLEAN, `${node.text!} ∈ boolean`]);
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
        if ((operator.kind === "DotToken" || operator.kind === "QuestionDotToken") && left.varId !== undefined && right.varId !== undefined) {
          // 处理属性访问
          const propName = right.text;
          if (propName) {
            allConstraints.push(["takeProperty", node.varId!, left.varId!, `${left.text!}.${propName}`]);
          }
        }
      }
    },
    // New运算符
    NewExpression(node) {
      if (node.children) {
        const classNode = node.children.find(n => n.kind === "Identifier");
        if (classNode?.varId !== undefined) {
          allConstraints.push(["sameType", node.varId!, classNode.varId, `new ${classNode.text!}`]);
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
    // 处理返回值
    ReturnStatement(node) {
      if (node.children && node.children.length >= 2) {
        const exprNode = node.children[1];

        let funcNode = node.parent;
        while (funcNode && funcNode.kind !== "FunctionDeclaration" && funcNode.kind !== "MethodDeclaration") funcNode = funcNode.parent;
        funcNode = funcNode?.children?.find(n => n.kind === "Identifier");

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
      if (node.children && node.children.length >= 2) {
        // 不能改为在bindings中查找，因为有可能是匿名函数调用
        const funcNode = node.children[0];
        if (funcNode.varId !== undefined && node.varId !== undefined) {
          allConstraints.push(["funcCall", node.varId, funcNode.varId, `${node.text}`]);
        }
      }
    },
    // 处理箭头函数 () => {}
    ArrowFunction(node) {
      // 如果没有block，退出作用域，必须postOrder!
      if (!node.children?.some(n => n.kind === "Block")) {
        const previous = scopeStack.pop();
        if (previous) {
          if (LOG_SCOPE) {
            console.log(`ArrowFunction at line ${node.position?.start?.line}, column ${node.position?.start?.character} in ${filePath}`);
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
          console.log(`Variable bindings end at line ${node.position?.start?.line}, column ${node.position?.start?.character} in ${filePath}:`);
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

  // 解析导入路径
  function resolveImportPath(currentFilePath: string, importSpecifier: string): string | undefined {
    if (importSpecifier.startsWith(".")) {
      // 本地模块：相对路径 + 补后缀
      const realCurrentPath = path.basename(currentFilePath).replace(/\^/g, "\\").replace(/\.ast\.json/g, "");
      const absbase = path.resolve(path.dirname(realCurrentPath), importSpecifier);
      const base = path.relative(process.cwd(), absbase);
      for (const extname of [".ts", ".js", ".ets", ".tsx", ".d.ts", ".d.ets"]) {
        const ret = base + extname;
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

  function walk(node: AstNode) {
    const id = node.varId;
    if (id === undefined) throw new Error("Missing varId in second pass");
    syntaxNodes[id] = { kind: node.kind, text: node.text, file: filePath, position: node.position };

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

// 求解类型图
function deriveVariableTypes() {
  for (let [kind, a, b] of allConstraints) {
    a = find(Number(a));
    if (kind === "hasType") {
      if (syntaxNodes[a].kind === "Identifier") {
        graph[a] ??= {};
      }
      typeSet[a] = b; source[a] ??= {};
    } else if (kind !== "sameID") {
      b = find(Number(b));
      if (b === a) continue; // 避免自引用
      graph[b] ??= {}; graph[b][a] = kind;
      source[a] ??= {}; source[a][b] = UNKNOWN;
    }
  }

  worklist = Object.keys(typeSet).map(Number);
  while (worklist.length > 0) {
    const cur = worklist.pop()!;
    cnt[cur] = (cnt[cur] ?? 0) + 1;
    if (cnt[cur] > 20000) {
      console.warn(`Node ${cur} has too many iterations (${cnt[cur]}), possible infinite loop`);
      break;
    }
    if (LOG_TYPE_FLOW) {
      console.log(`Processing node ${cur} (${syntaxNodes[cur]?.text}) with ${cnt[cur]} iterations:`);

      // 输出 Types
      if (typeSet[cur]) {
        console.log(`  Type (raw): ${typeSet[cur]}`);
        console.log(`  Type: ${JSON.stringify(typeNodes[typeSet[cur]])}`);
      } else {
        console.log(`  Type: no types`);
      }
    }

    let tSet = typeSet[cur];
    if(!tSet) {
      console.warn(`node ${cur} with no type`);
      continue;
    }
    for (const nextStr in graph[cur] || []) {
      const next = Number(nextStr);
      const nSet = typeSet[next];


      //  数据流处理
      if (graph[cur][next] === "sameType" || graph[cur][next] === "annotation") {
        // 如果是同类型
        source[next][cur] = tSet;
        typeSet[next] = mergeBranches(next);
      }
      else if (graph[cur][next] === "takeProperty") {
        // 如果是取属性，添加属性类型
        const propName = syntaxNodes[next]?.text!.split(".").pop();
        if (propName && typeNodes[tSet] && typeNodes[tSet].kind == "object" && propName in typeNodes[tSet].properties) {
          source[next][cur] = typeNodes[tSet].properties[propName];
          if (LOG_TYPE_FLOW)
            console.log(`takeProperty[object] ${typeNodes[tSet].properties[propName]} for ${propName} in edge ${cur}->${next}`);
        } else if (propName && typeNodes[tSet] && typeNodes[tSet].kind == "enum" && propName in typeNodes[tSet].members) {
          source[next][cur] = typeNodes[tSet].members[propName];
          if (LOG_TYPE_FLOW)
            console.log(`takeProperty[enum] ${typeNodes[tSet].members[propName]} for ${propName} in edge ${cur}->${next}`);
        }
        typeSet[next] = mergeBranches(next);
      }
      else if (graph[cur][next] === "arrayElement") {
        // 取数组成员
        if (typeNodes[tSet]?.kind === "array") {
          source[next][cur] = typeNodes[tSet].elementType;
        } else {
          console.warn(`Unexpected arrayElement when type ${tSet} : ${printType(tSet)} is not array in edge ${cur}->${next}`);
        }
        typeSet[next] = mergeBranches(next);
      }
      else if (graph[cur][next] === "makeArray") {
        // 如果是数组类型，添加元素类型
        const id = newTypeNode({ kind: "array", elementType: tSet });
        source[next][cur] = id;
        typeSet[next] = mergeBranches(next);
      }
      else if (graph[cur][next] === "funcCall") {
        // 如果是函数调用，添加函数返回类型
        if (typeNodes[tSet]?.kind === "function") {
          source[next][cur] = typeNodes[tSet].returnType;
        } else {
          console.warn(`Unexpected funcCall when type ${tSet} : ${printType(tSet)} is not function in edge ${cur}->${next}`);
        }
        typeSet[next] = mergeBranches(next);
      }
        



      // 控制流处理
      else if (graph[cur][next] === "setProperty") {
        // 如果是设置属性，添加属性类型
        const propName = syntaxNodes[cur]?.text;


        if (nSet === undefined) {
          console.warn(`setProperty on undefined type in edge ${cur}->${next}`);
          continue;
        }
        if (typeNodes[nSet] === undefined || typeNodes[nSet].kind !== "object") {
          console.warn(`setProperty on non-object type ${printType(nSet)} in edge ${cur}->${next}`);
          continue;
        }
        if (!propName) {
          console.warn(`setProperty with no propName in edge ${cur}->${next}`);
          continue;
        }


        const id = newTypeNode({ kind: "object", name: typeNodes[nSet].name, properties: makePurePropertiesCopy(typeNodes[nSet].properties, propName, tSet)});
        typeSet[next] = id;
      }
      else if (graph[cur][next] === "setPramType") {
        // 如果是参数类型，添加参数类型
        const paramName = syntaxNodes[cur]?.text;


        if (nSet === undefined) {
          console.warn(`setPramType on undefined type in edge ${cur}->${next}`);
          continue;
        }
        if (typeNodes[nSet] === undefined || typeNodes[nSet].kind !== "function") {
          console.warn(`setPramType on non-function type ${printType(nSet)} in edge ${cur}->${next}`);
          continue;
        }
        if (!paramName) {
          console.warn(`Parameter name not found in edge ${cur}->${next}`);
          continue;
        }


        source[next][cur] = tSet;
        let tylist : number[]  = [];
        for(const srcStr in source[next]) {
          const src = Number(srcStr);
          const curParamName = syntaxNodes[cur]?.text;
          if (curParamName !== paramName) continue;
          tylist.push(source[next][src]);
        }
        typeSet[next] = newTypeNode({ kind: "function", params: [...typeNodes[nSet].params.filter(pa => pa.name !== paramName), {name: paramName, type: mergeTypes(tylist)}], returnType: typeNodes[nSet].returnType });
      }
      else if (graph[cur][next] === "returnType" || graph[cur][next] === "returnAnnotation") {
        // 如果是返回类型，添加返回类型
        if (nSet === undefined) {
          console.warn(`returnType or returnAnnotation on undefined type in edge ${cur}->${next}`);
          continue;
        }
        if (typeNodes[nSet] === undefined || typeNodes[nSet].kind !== "function") {
          console.warn(`returnType or returnAnnotation on non-function type ${printType(nSet)} in edge ${cur}->${next}`);
          continue;
        }

        
        source[next][cur] = tSet;
        typeSet[next] = newTypeNode({ kind: "function", params: typeNodes[nSet].params, returnType: mergeBranches(next, ["returnType", "returnAnnotation"]) });
      }




      // 更新传播
      if(typeSet[next] !== nSet && typeSet[next] !== UNKNOWN) worklist.push(next);
    }
  }

  const result: Record<string, string> = {};
  for (const [name, id] of globalVarBindings.entries()) {
    result[name] = printType(typeSet[id] ?? UNKNOWN);
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
    if (kind === "sameID") {
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
      const srcVar = syntaxNodes[srcId];
      const srcfile = syntaxNodes[srcId]?.file || "unknown";
      if (!seen.has(srcId)) {
        nodes.push({
          id: srcId,
          label: srcVar?.text || `var_${srcId}`,
          typeid: typeSet[srcId] ?? UNKNOWN,
          type: printType(typeSet[srcId] ?? UNKNOWN),
          fullType: printFullType(typeSet[srcId] ?? UNKNOWN),
          text: srcVar?.text,
          file: srcfile,
          position: srcVar?.position,
        });
        seen.add(srcId);
      }

      for (const dstIdStr in dsts) {
        const dstId = Number(dstIdStr);
        const dstVar = syntaxNodes[dstId];
        const dstfile = syntaxNodes[dstId]?.file || "unknown";
        if (!seen.has(dstId)) {
          nodes.push({
            id: dstId,
            label: dstVar?.text || `var_${dstId}`,
            typeid: typeSet[dstId] ?? UNKNOWN,
            type: printType(typeSet[dstId] ?? UNKNOWN),
            fullType: printFullType(typeSet[dstId] ?? UNKNOWN),
            text: dstVar?.text,
            file: dstfile,
            position: dstVar?.position,
          });
          seen.add(dstId);
        }

        edges.push({ from: srcId, to: dstId, label: dsts[dstIdStr] });
      }
    }

    return { nodes, edges };
  }
}


// 主流程
function main() {
  // 创建一个虚拟节点，表示未知的导入
  syntaxNodes[0] = { kind: "null", text: "unknown import hole", file: "null", position: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } } };
  // 手动初始化内置类型节点
  typeNodes[NUMBER] = { kind: "primitive", name: "number" };
  typeNodes[STRING] = { kind: "primitive", name: "string" };
  typeNodes[BOOLEAN] = { kind: "primitive", name: "boolean" };
  typeNodes[ANY] = { kind: "primitive", name: "any" };
  typeNodes[UNKNOWN] = { kind: "primitive", name: "unknown" };
  typeNodes[VOID] = { kind: "primitive", name: "void" };
  typeNodes[NULL] = { kind: "primitive", name: "null" };
  typeNodes[UNDEFINED] = { kind: "primitive", name: "undefined" };
  typeNodes[NEVER] = { kind: "primitive", name: "never" };
  typeNodes[REGEXP] = { kind: "primitive", name: "RegExp" };
  typeNodes[BIGINT] = { kind: "primitive", name: "bigint" };
  // 初始化类型集合
  typeSet[VOID] = VOID;
  // 初始化typeNodeReverseMap
  for (const [id, node] of Object.entries(typeNodes)) {
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
