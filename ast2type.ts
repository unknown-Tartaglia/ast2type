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
  | { kind: "object"; name : string; properties: Record<string, number> };


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
const typeSet: Record<number, Set<number>> = {};
const del: Record<number, Set<number>> = {};
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

function printTypeSet(typeIds: Set<number>): string {
  if (!typeIds || typeIds.size === 0) return "unknown";
  return Array.from(typeIds)
    .map((id) => printType(id))
    .join(" | ");
}

// 递归打印类型
function printType(n: number): string {
  const occur : Record<string, number> = {};
  return helper(n);
  function helper(n: number): string {
    const t = typeNodes[n];
    if (!t)
    {
      // console.warn(`Type ID ${n} not found in typeNodes`);
      return "impossible! type unknown";
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
      default:
        return "impossible type";
    }
  }
}

function printFullTypeSet(typeIds: Set<number>): string {
  if (!typeIds || typeIds.size === 0) return "unknown";
  return Array.from(typeIds)
    .map((id) => printFullType(id))
    .join(" | ");
}

// 打印完整类型
function printFullType(n: number): string {
  const occur : Record<string, number> = {};
  return helper(n);
  function helper(n: number): string {
    const t = typeNodes[n];
    if (!t)
    {
      // console.warn(`Type ID ${n} not found in typeNodes`);
      return "impossible! type unknown";
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
      default:
        return "impossible type";
    }
  }
}

// 序列化 TypeNode 为字符串, 确保唯一性
function serializeTypeNode(t: TypeNode): string {
  // console.log(`Serializing type node: ${JSON.stringify(t)}`);
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
  }
}

function newTypeNode(ty: TypeNode): [number, number[]] {  
  console.log(`allocating new type node: ${JSON.stringify(ty)} ~~~ ${serializeTypeNode(ty)}`);
  let serialized = serializeTypeNode(ty);
  if (typeNodeReverseMap.has(serialized)) {
    const id = typeNodeReverseMap.get(serialized);
    return [id!, []];
  }
  const id = typeVarCounter++;
  typeNodes[id] = ty;
  typeNodeReverseMap.set(serialized, id);
  console.log(`Initial new type node: ${id} : ${serialized}`);  

  // 处理对象类型的循环引用
  const occur : Record<string, number> = {};
  let del : number[] = [];
  helper(id);
  function helper(n: number): number {
    const t = {...typeNodes[n]};
    if (!t) {
      // console.warn(`Type ID ${n} not found in typeNodes`);
      return n; // 返回原ID
    }
    if (t.kind === "array") {
      const ret = helper(t.elementType);
      if (t.elementType !== ret) {
        del.push(t.elementType);
        t.elementType = ret;
      }
    }
    else if (t.kind === "function") {
      for (const param of t.params) {
        const ret = helper(param.type);
        if (param.type !== ret) {
          del.push(param.type);
          param.type = ret;
        }
      }
      const returnType = helper(t.returnType);
      if (t.returnType !== returnType) {
        del.push(t.returnType);
        t.returnType = returnType;
      }
    } else if (t.kind === "union") {
      const newTypes = t.types.map(helper);
      for (const type of t.types) {
        if (!newTypes.includes(type)) del.push(type);
      }
      t.types = newTypes;
    } else if (t.kind === "object") {
      if (occur[t.name]) {
        // console.log(`Object type ${t.name} already processed, skipping...`);
        return occur[t.name];
      }
      occur[t.name] = n;
      // console.log(`Object type ${t.name} with properties:`, t.properties);  
      for (const key in t.properties) {
        const ret = helper(t.properties[key]);
        if (t.properties[key] !== ret) {
          del.push(t.properties[key]);
          t.properties[key] = ret;
        }
      }
      delete occur[t.name];
    }
    // console.log(`Processed type node: ${n} in ${id} : ${JSON.stringify(t)}`);
    if(n === id) {
      typeNodes[id] = t;
      return id
    }
    else {
      serialized = serializeTypeNode(t);
      if (typeNodeReverseMap.has(serialized)) {
        const id = typeNodeReverseMap.get(serialized)!;
        console.log(`Type node already exists: ${id} : ${printType(id)} ~~~ ${serialized}`);
        return id;
      } else {
        const id = typeVarCounter++;
        typeNodes[id] = t;
        typeNodeReverseMap.set(serialized, id);
        console.log(`New type node created: ${id} : ${printType(id)} ~~~ ${serialized}`);
        return id;
      }
    }
  }

  serialized = serializeTypeNode(typeNodes[id]);
  console.log(`New type node created: ${id} : ${printType(id)} ~~~ ${serialized}`);
  typeNodeReverseMap.set(serialized, id);
  if (del.length > 0) {
    console.log(`Type node ${id} has deleted types: ${del.map(printType).join(", ")}`);
  }
  return [id, del];
}


// 第一遍：标号并提取export
function firstPass(filePath: string, ast: AstNode) {
  function walk(node: AstNode) {
    node.varId = getTypeVarId(node);
    for (const child of node.children || []) {
      child.parent = node;
      walk(child);
    }

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
  const varBindings = new Map<string, number>();

  const preOrderHandlers: Record<string, (node: AstNode) => void> = {
    // 处理函数声明
    FunctionDeclaration(node) {
      if (node.children) {
        const idNode = node.children?.find(n => n.kind === "Identifier");
        if (idNode && idNode.varId !== undefined && idNode.text) {
          varBindings.set(idNode.text, idNode.varId!);
        }

        typeSet[idNode?.varId!] = new Set();

        const index = node.children?.findIndex(n => n.kind === "ColonToken");
        // 类型注解
        if (index !== undefined && index !== -1) {
          const typeNode = node.children?.[index + 1];
          if (typeNode && typeNode.varId) {
            const [id] = newTypeNode({ kind: "function", params: [], returnType: UNKNOWN });
            typeSet[idNode?.varId!].add(id);
            allConstraints.push(["returnAnnotation", idNode?.varId!, typeNode.varId, `return type of function ${idNode?.text!}`]);
          }
        }
        else if (findNodesByKind(node, "ReturnStatement").length === 0) {
          // 如果没有返回类型注解并且没有Return语句
          const [id] = newTypeNode({ kind: "function", params: [], returnType: VOID });
          typeSet[idNode?.varId!].add(id);
        }
        else {
          const [id] = newTypeNode({ kind: "function", params: [], returnType: UNKNOWN });
          typeSet[idNode?.varId!].add(id);
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
      varBindings.set(left.text!, left.varId!);
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
    // 处理函数参数
    Parameter(node) {
      if (node.children) {
        const paramIdNode = node.children?.find(n => n.kind === "Identifier");
        if (!paramIdNode || !paramIdNode.varId) return;
        varBindings.set(paramIdNode.text!, paramIdNode.varId!);

        // 处理类型注解
        const colonIndex = node.children?.findIndex(n => n.kind === "ColonToken");
        if (colonIndex !== undefined && colonIndex !== -1) {
          const typeNode = node.children?.[colonIndex + 1];
          if (typeNode && typeNode.varId) {
            allConstraints.push(["annotation", paramIdNode.varId!, typeNode.varId, `annotation ${paramIdNode.text!} : ${typeNode.text!}`]);
            return 
          }
        }

        let funcIdNode = node.parent;
        while(funcIdNode && funcIdNode.kind !== "FunctionDeclaration" && funcIdNode.kind !== "MethodDeclaration") funcIdNode = funcIdNode.parent;
        funcIdNode = funcIdNode?.children?.find(n => n.kind === "Identifier");
        if (!funcIdNode || !funcIdNode.varId) return;

        allConstraints.push(["paramType", funcIdNode.varId!, paramIdNode.varId!, `parameter ${paramIdNode.text!} in function ${funcIdNode.text!}`]);
      }
    },
    // 处理class声明
    ClassDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        const idNode = node.children?.filter(n => n.kind === "Identifier")[0];
        if (idNode && idNode.varId) {
          const [typeId] = newTypeNode({ kind: "object", name: idNode.text!, properties: {} });
          console.log(`Class ${idNode.text} has type ID ${typeId}`);
          typeSet[idNode.varId] = new Set([typeId]);
          varBindings.set(idNode.text!, idNode.varId!);
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
        varBindings.set(symbol, idNode.varId!);
        if (symbol === "window") {
          console.warn(`Identifier ${idNode.varId!}: ${symbol} in import declaration`);
        }
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
      const [id] = newTypeNode({ kind: "object", name: "Object", properties: {} });
      allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ Object`]);
    },
    ThisKeyword(node) {
      if (node.varId === undefined) return;
      // this关键字通常在类方法中使用
      let classNode = node.parent;
      while(classNode && classNode.kind !== "ClassDeclaration") classNode = classNode.parent;
      if (classNode && classNode.varId !== undefined) {
        // 在类中this指向当前类实例
        const idNode = classNode.children?.find(n => n.kind === "Identifier");
        if (idNode && idNode.varId !== undefined) {
          allConstraints.push(["sameType", node.varId, idNode.varId, `this in class ${idNode.text!}`]);
          return;
        }
      }
    },
    LiteralType(node) {
      if (node.varId === undefined) return;
      const [id] = newTypeNode({ kind: "primitive", name: node.text || "unknown LiteralType" });
      allConstraints.push(["hasType", node.varId, id, `${node.text!} ∈ ${node.text!}`]);
    },
    ArrayType(node) {
      if (node.children && node.children.length >= 3) {
        const elementTypeNode = node.children[0];
        if (elementTypeNode.varId !== undefined && node.varId !== undefined) {
          allConstraints.push(["makeArray", node.varId, elementTypeNode.varId, `${node.text!} ∈ ${printType(elementTypeNode.varId)}[]`]);
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
          allConstraints.push(["sameType", node.varId!, idNode.varId, `TypeReference ${idNode.text!}`]);
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
        const typeId = varBindings.get(node.text);

        if(node.text === "window") {
          console.warn(`Identifier ${node.varId!}: ${node.text}`);
          if (typeId === undefined) {
            console.warn(`Identifier ${node.text} not found in varBindings`);
          }
        }

        if (typeId !== undefined) {
          allConstraints.push(["sameID", node.varId!, typeId, `same identifier: ${node.text!}`]);
        }
        else {
          // varBindings.set(node.text, node.varId!);
          // console.warn(`Identifier ${node.text} not found in varBindings, using its own varId ${node.varId}`);
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
        if (idNode && idNode.varId !== undefined) {
          const [typeId] = newTypeNode({ kind: "object", name: idNode.text!, properties: {} });
          typeSet[idNode.varId] = new Set([typeId]);
          varBindings.set(idNode.text!, idNode.varId!);
        }
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
        if (!propIdNode || propIdNode.varId === undefined) return;

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
    // 处理classProperty
    PropertyDeclaration(node) {
      if (node.children && node.children.length >= 2) {
        let idNode = node.parent;
        while (idNode && idNode.kind !== "ClassDeclaration") idNode = idNode.parent;
        idNode = idNode?.children?.find(n => n.kind === "Identifier");
        if (!idNode || idNode.varId === undefined) return;

        const propIdNode = findNodesByKind(node, "Identifier")[0];
        if (!propIdNode || propIdNode.varId === undefined) return;

        const colonNode = findNodesByKind(node, "ColonToken")[0];
        if (colonNode === undefined || colonNode.varId === undefined) {
          allConstraints.push(["setProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
          return;
        } else {
          const index = colonNode!.parent!.children?.findIndex(n => n.kind === "ColonToken");

          // 处理类型注解
          if (index !== undefined && index !== -1) {
            const typeNode = colonNode!.parent!.children?.[index + 1];
            if (typeNode && typeNode.varId) {
              allConstraints.push(["setProperty", idNode.varId!, propIdNode.varId!, `${idNode.text!}.${propIdNode.text!}`]);
              allConstraints.push(["annotation", propIdNode.varId, typeNode.varId, `annotation ${idNode.text!}.${propIdNode.text!} : ${typeNode.text!}`]);
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
          typeSet[propIdNode.varId] = new Set();
          
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
          
          const [typeId] = newTypeNode(funcType);
          typeSet[propIdNode.varId].add(typeId);

          allConstraints.push(["setProperty", idNode.varId, propIdNode.varId, `${propIdNode.text!}() => ${printType(typeId)}`]);
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
          allConstraints.push(["returnType", node.varId!, VOID, `return;`]);
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
    }
  }

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


  for (const [name, id] of varBindings.entries()) {
    if (!globalVarBindings.has(name)) {
      globalVarBindings.set(name, id);
    } else {
      // 如果已经存在，合并类型
      const existingId = globalVarBindings.get(name)!;
      allConstraints.push(["sameType", id, existingId, `merge type for ${name}`]);
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
      typeSet[a] ??= new Set();
      typeSet[a].add(b);
    } else if (kind !== "sameID") {
      b = find(Number(b));
      if (b === a) continue; // 避免自引用
      graph[b] ??= {}; graph[b][a] = kind;
    }
  }

  const worklist = Object.keys(typeSet).map(Number);
  while (worklist.length > 0) {
    const cur = worklist.pop()!;
    cnt[cur] = (cnt[cur] ?? 0) + 1;
    if(cnt[cur] >200) {
      console.warn(`Node ${cur} has too many iterations (${cnt[cur]}), possible infinite loop`);
      break;
    }
    console.log(`Processing node ${cur} (${syntaxNodes[cur]?.text}) with ${cnt[cur]} iterations : ${typeSet[cur].size}, ${typeSet[cur] ? [...typeSet[cur]].map(printType).join(" | ") : "no types"}, ${del[cur] ? [...del[cur]].map(printType).join(" | ") : "no deleted types"}`);
    const tSet = typeSet[cur] ?? new Set();
    for (const nextStr in graph[cur] || []) {
      const next = Number(nextStr);
      const nSet = typeSet[next] ?? new Set();
      let changed = false;
      del[next] ??= new Set();
      for (const d of del[cur] || []) {
        if(nSet.delete(d)) {
          console.log(`Deleting ${d} from ${next} due to ${cur} -> ${next} (${graph[cur][next]})`);
        }
        del[next].add(d);
      }
      const before = nSet.size;



      if (graph[cur][next] === "sameType" || graph[cur][next] === "annotation") {
        // 如果是同类型，直接合并
        for (const t of tSet) if(!del[cur]?.has(t)) nSet.add(t);
        if (nSet.size > before)
          changed = true;
      }
      else if (graph[cur][next] === "setProperty") {
        // 如果是设置属性，添加属性类型
        const propName = syntaxNodes[cur]?.text;

        if (nSet.size !== 1) {
          console.warn(`Unexpected setProperty with multiple types: ${[...nSet].map(printType).join(" | ")}`);
          continue;
        }
        const nType = nSet.values().next().value;
        if (nType === undefined) {
          console.warn(`setProperty on undefined type in node ${next}`);
          continue;
        }
        if(typeNodes[nType] === undefined || typeNodes[nType].kind !== "object") {
          console.warn(`setProperty on non-object type ${printType(nType)} in node ${next}`);
          continue;
        }
        if (!propName) {
          console.warn(`Property name not found in node ${next}`);
          continue;
        }

        for (const t of tSet) {
          if (propName in typeNodes[nType].properties) {
            // 取出属性类型
            const propType : number = typeNodes[nType].properties[propName];
            

            if (propType !== undefined && propType !== UNKNOWN) {
              if (typeNodes[propType]?.kind === "union" && typeNodes[propType].types) {
                // 如果属性类型是联合类型，添加到联合类型中
                const [id, d1] = newTypeNode({ kind: "union", types: [...typeNodes[propType].types.filter(n => !del[cur]?.has(n)), t] });
                const [id2, d2] = newTypeNode({ kind: "object", name: typeNodes[nType].name ,properties: { ...typeNodes[nType].properties, [propName]: id } });
                nSet.delete(nType); nSet.add(id2);
                changed = true;
                del[next].add(nType);
                del[next].add(propType);
                for (const d of d1) del[next].add(d);
                for (const d of d2) del[next].add(d);
                console.log(`deleting ${nType}:${serializeTypeNode(typeNodes[nType])} and ${propType}:${serializeTypeNode(typeNodes[propType])} from ${next}, adding ${id2}:${serializeTypeNode(typeNodes[id2!])} in SetProrperty`);
              } else if (!del[cur].has(propType) && propType !== UNKNOWN && propType !== t) {
                // 如果属性类型不同，创建联合类型
                const [id, d1] = newTypeNode({ kind: "union", types: [propType, t] });
                const [id2, d2] = newTypeNode({ kind: "object", name: typeNodes[nType].name ,properties: { ...typeNodes[nType].properties, [propName]: id } });
                nSet.delete(nType); nSet.add(id2);
                changed = true;
                del[next].add(nType);
                del[next].add(propType);
                for (const d of d1) del[next].add(d);
                for (const d of d2) del[next].add(d);
                console.log(`deleting ${nType}:${serializeTypeNode(typeNodes[nType])} and ${propType}:${serializeTypeNode(typeNodes[propType])} from ${next}, adding ${id2}:${serializeTypeNode(typeNodes[id2!])} in SetProrperty`);
              }
              else {
                // 直接更新属性类型
                const [id2, d2] = newTypeNode({ kind: "object", name: typeNodes[nType].name ,properties: { ...typeNodes[nType].properties, [propName]: t } });
                for (const d of d2) del[next].add(d);
                console.log(`Updating property ${propName} from ${propType}:${serializeTypeNode(typeNodes[propType])} to ${t}:${serializeTypeNode(typeNodes[t])}`);
                if (id2 === nType) {
                  console.log(`setProperty created the same type ${serializeTypeNode(typeNodes[id2])} as the original type ${serializeTypeNode(typeNodes[nType])}`);
                }
                else {
                  nSet.delete(nType); nSet.add(id2);
                  changed = true;
                  del[next].add(nType);
                  del[next].add(propType);
                  console.log(`deleting ${nType}:${serializeTypeNode(typeNodes[nType])} and ${propType}:${serializeTypeNode(typeNodes[propType])} from ${next}, adding ${id2}:${serializeTypeNode(typeNodes[id2!])} in SetProrperty`);
                }
              }
            }
          } else {
            // 如果属性不存在，添加一个新的属性类型
            const [id2, d2] = newTypeNode({ kind: "object", name: typeNodes[nType].name ,properties: { ...typeNodes[nType].properties, [propName]: t } });
            for (const d of d2) del[next].add(d);
            nSet.delete(nType); nSet.add(id2);
            changed = true;
            del[next].add(nType);
            console.log(`deleting ${nType}:${serializeTypeNode(typeNodes[nType])} from ${next}, adding ${id2}:${serializeTypeNode(typeNodes[id2])}`);
          }
        }
      }
      else if (graph[cur][next] === "takeProperty") {
        // 如果是取属性，添加属性类型
        for (const t of tSet) {
          const propName = syntaxNodes[next]?.text!.split(".").pop();
          // console.log(`Processing property ${propName} for type ${t} in node ${next}`);
          if (propName && typeNodes[t] && typeNodes[t].kind == "object" && propName in typeNodes[t].properties) {
            nSet.add(typeNodes[t].properties[propName]);
            // console.log(`Adding property type ${property[t][propName]} for ${propName} in node ${next}`);
          }
        }
        if (nSet.size > before)
          changed = true;
      }
      else if (graph[cur][next] === "arrayElement") {
        // 去掉数组括号
        for (const t of tSet) {
          if (typeNodes[t]?.kind === "array") {
            nSet.add(typeNodes[t].elementType);
          }
        }
        if (nSet.size > before)
          changed = true;
      }
      else if (graph[cur][next] === "makeArray") {
        // 如果是数组类型，添加元素类型
        for (const t of tSet) {
          const [id, d] = newTypeNode({ kind: "array", elementType: t });
          for (const id of d) del[next].add(id);
          nSet.add(id);
        }
        if (nSet.size > before)
          changed = true;
      }
      else if (graph[cur][next] === "funcCall") {
        // 如果是函数调用，添加函数返回类型
        for (const t of tSet) {
          if (typeNodes[t]?.kind === "function" && typeNodes[t].returnType != UNKNOWN) {
            nSet.add(typeNodes[t].returnType);
          }
        }
        if (nSet.size > before)
          changed = true;
      }
      else if (graph[cur][next] === "paramType") {
        // 如果是参数类型，添加参数类型
        if(tSet.size !== 1)
          console.warn(`Unexpected paramType with multiple types: ${[...tSet].map(printType).join(" | ")}`);
        else {
          const paramType = tSet.values().next().value;
          const paramName = syntaxNodes[cur]?.text;
          if (nSet.size === 1 ) {
            // 如果已经有函数类型，添加参数
            const existingType = nSet.values().next().value;
            const ty = typeNodes[existingType!];
            if (existingType && ty && ty.kind === "function" && paramName && paramType) {
              const [id, d] = newTypeNode({ kind: "function", params: [...ty.params, { name: paramName, type: paramType }], returnType: ty.returnType });
              for (const id of d) del[next].add(id);
              nSet.delete(existingType); nSet.add(id);
              changed = true;
              del[next].add(existingType);
              console.log(`deleting ${existingType}:${serializeTypeNode(typeNodes[existingType])} from ${next}, adding ${id}:${serializeTypeNode(typeNodes[id])}`);
            }
          }
        }
      }
      else if (graph[cur][next] === "returnType" || graph[cur][next] === "returnAnnotation") {
        // 如果是返回类型，添加返回类型
        for (const returnType of tSet) {
          if (nSet.size === 1) {
            // 如果已经有函数类型，设置返回类型
            const existingType = nSet.values().next().value;
            const ty = typeNodes[existingType!];
            if (!ty || !existingType || !returnType) {
              console.warn(`error in returnType processing`);
              continue;
            }
            if (ty.kind === "function") {
              const existingReturnType = ty.returnType;
              if (typeNodes[existingReturnType]?.kind === "union" && typeNodes[existingReturnType].types) {
                const [id, d] = newTypeNode({ kind: "union", types: [...typeNodes[existingReturnType].types.filter(n => !del[cur].has(n)), returnType] });
                const [id2, d2] = newTypeNode({ kind: "function", params: ty.params, returnType: id });
                for (const id of d) del[next].add(id);
                for (const id of d2) del[next].add(id);
                nSet.delete(existingType); nSet.add(id2); del[next].add(existingType); del[next].add(existingReturnType);
                console.log(`deleting ${existingType}:${serializeTypeNode(typeNodes[existingType])} and ${printType(existingReturnType)} from ${next}, adding ${id2}:${serializeTypeNode(typeNodes[id2])}`);
                changed = true;
              }
              else if (!del[cur]?.has(existingReturnType) && existingReturnType !== returnType && existingReturnType !== UNKNOWN) {
                // 如果返回类型不同，且不是要删除的类型，创建联合类型
                const [id, d] = newTypeNode({ kind: "union", types: [existingReturnType, returnType] });
                const [id2, d2] = newTypeNode({ kind: "function", params: ty.params, returnType: id });
                for (const id of d) del[next].add(id);
                for (const id of d2) del[next].add(id);
                nSet.delete(existingType); nSet.add(id2); del[next].add(existingType); del[next].add(existingReturnType);
                console.log(`deleting ${existingType}:${serializeTypeNode(typeNodes[existingType])} and ${printType(existingReturnType)} from ${next}, adding ${id2}:${serializeTypeNode(typeNodes[id2])}`);
                changed = true;
              }
              else {
                if (existingType) {
                  const [id, d] = newTypeNode({ kind: "function", params: ty.params, returnType });
                  for (const id of d) del[next].add(id);
                  if (id !== existingType) {
                    nSet.delete(existingType); nSet.add(id); 
                    changed = true;
                    del[next].add(existingType); del[next].add(existingReturnType);
                    console.log(`deleting ${existingType}:${serializeTypeNode(typeNodes[existingType])} and ${printType(existingReturnType)} from ${next}, adding ${id}:${serializeTypeNode(typeNodes[id])}`);
                  }
                }
              }
            }
          } else {
            // 如果没有函数类型，直接添加返回类型
            const [id, d] = newTypeNode({ kind: "function", params: [], returnType });
            for (const id of d) del[next].add(id);
            nSet.add(id);
            changed = true;
            console.log(`Adding return type ${printType(id)} to node ${next}`);
            // 遍历graph寻找参数节点
            for (const [src, dsts] of Object.entries(graph)) {
              const srcId = Number(src);
              for (const dstIdStr in dsts) {
                const dstId = Number(dstIdStr);
                if (dstId === next) {
                  if (graph[srcId][dstId] === "paramType") {
                    // 如果是参数类型
                    worklist.push(srcId); 
                  }
                } 
              }
            }
          }
        }
      }
      if (changed) {
        typeSet[next] = nSet;
        worklist.push(next);
      }
    }
  }

  const result: Record<string, string> = {};
  for (const [name, id] of globalVarBindings.entries()) {
    result[name] = printTypeSet(typeSet[id]);
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
          type: printTypeSet(typeSet[srcId]),
          fullType: printFullTypeSet(typeSet[srcId]),
          text: srcVar?.text,
          file: srcfile,
          position: srcVar?.position,
          title: `Types: ${[...(typeSet[srcId] ?? [])].sort().join(" | ")}\nText: ${srcVar?.text}\nPos: ${JSON.stringify(srcVar?.position)}`
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
            type: printTypeSet(typeSet[dstId]),
            fullType: printFullTypeSet(typeSet[dstId]),
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
  typeSet[VOID] = new Set([VOID]);
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
