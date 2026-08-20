import { DEDUCE_ONLY_WHEN_ALL_KNOWNN, LOG_TYPE_FLOW, LOG_TYPENODE, LOG_TYPENODE_VERBOSE, meta, solver, tNode } from "../ast2type";
import { VarId } from "./fact";
import * as ts from "typescript";

export class tNodeStore {
    private typeNodes: nType[] = [];
    private hash: Map<nType, string> = new Map();
    private reverseMap: Map<string, TypeId> = new Map();
    type2state: Map<TypeId, Set<NodeState>> = new Map();
    ANY = 0;
    UNKNOWN = 1;
    NUMBER = 2;
    STRING = 3;
    BOOLEAN = 4;
    UNDEFINED = 5;
    VOID = 6;
    private _synthObjId = 100000;
    /** Agent 反馈可以保留内部图无法建模但语法合法的泛型文本；GT 仍保持保守解析。 */
    private allowOpaqueGenerics = false;

    constructor() {
        // 预定义一些基础类型
        this.typeNodes.push({ kind: "primitive", name: "any" });    // 0: any
        this.typeNodes.push({ kind: "primitive", name: "unknown" }); // 1: unknown
        this.typeNodes.push({ kind: "primitive", name: "number" });  // 2: number
        this.typeNodes.push({ kind: "primitive", name: "string" });  // 3: string
        this.typeNodes.push({ kind: "primitive", name: "boolean" }); // 4: boolean
        this.typeNodes.push({ kind: "primitive", name: "undefined" }); // 5: undefined
        this.typeNodes.push({ kind: "primitive", name: "void" }); // 6: void
        for (let i = 0; i < this.typeNodes.length; i++) {
            const serialized = this.serialize(this.typeNodes[i]);
            this.reverseMap.set(serialized, i);
        }
    }

    private allocateTypeNode(t: nType): TypeId {
        const id = this.typeNodes.length;
        const serialized = this.serialize(t);
        this.typeNodes.push(t);
        this.reverseMap.set(serialized, id);
        if (LOG_TYPENODE) {
            console.log(`New type node created: ${id} : ${this.printFullType(id)}`);
        }
        return id;
    }

    // 修改TypeNode，危险操作，传播影响
    modifyTypeNode(id: number, t: nType) {
        if (LOG_TYPENODE) {
            console.log(`Change type node ${id} from ${JSON.stringify(this.typeNodes[id])} to ${JSON.stringify(t)}`);
        }
        if (id < 0 || id >= this.typeNodes.length) {
            console.warn(`modifyTypeNode: invalid TypeId ${id}`);
            return;
        }
        this.reverseMap.delete(this.serialize(this.typeNodes[id]));
        this.typeNodes[id] = t;
        this.reverseMap.set(this.serialize(t), id);
        // 传播影响
        const affectedStates = tNode.type2state.get(id)?.values();
        for (const state of affectedStates ?? []) {
            for (const node of solver.graph.state2node.get(state) ?? []) {
                solver.worklist.push(node);
                // console.log(`TypeNode ${node} affected by modification of TypeId ${id}, added to worklist`);
            }
        }
    }

    newTypeNode(ty: nType) {
        if (LOG_TYPENODE_VERBOSE) console.log(`allocating new type node: ${JSON.stringify(ty)} ~~~ ${this.serialize(ty)}`);
        let serialized = this.serialize(ty);
        if (this.reverseMap.has(serialized)) return this.reverseMap.get(serialized)!;

        // 处理对象类型的循环引用
        const occur: Map<TypeId, TypeId> = new Map();
        const helper = (t: nType): number => {
            if (!t) {
                // if (LOG_TYPENODE)
                console.warn(`Undefined typeNode in newTypeNode`);
                return this.UNKNOWN; // 返回UNKNOWN
            }
            switch (t.kind) {
                case "array": t.elementType = helper(this.typeNodes[t.elementType]); break;
                case "function":
                    if (occur.has(t.id)) {
                        return occur.get(t.id)!;
                    }
                    occur.set(t.id, this.UNKNOWN);

                    t.returnType = helper(this.typeNodes[t.returnType]);

                    // 处理参数
                    for (const idx in t.param) {
                        t.param[idx].type = helper(this.typeNodes[t.param[idx].type]);
                    }

                    if (occur.get(t.id) !== this.UNKNOWN && this.serialize(this.typeNodes[occur.get(t.id)!]) !== this.serialize(t)) {
                        this.modifyTypeNode(occur.get(t.id)!, t);
                        return occur.get(t.id)!;
                    }
                    break;
                case "union":
                    t.types = t.types.map(ty => helper(this.typeNodes[ty]));
                    break;
                case "object":
                    if (occur.has(t.id)) {
                        return occur.get(t.id)!;
                    }
                    occur.set(t.id, this.UNKNOWN);
                    for (const key in t.properties) {
                        t.properties[key] = helper(this.typeNodes[t.properties[key]]);
                    }

                    if (occur.get(t.id) !== this.UNKNOWN && this.serialize(this.typeNodes[occur.get(t.id)!]) !== this.serialize(t)) {
                        this.modifyTypeNode(occur.get(t.id)!, t);
                        return occur.get(t.id)!;
                    }
                    break;
            }
            serialized = this.serialize(t);
            if (this.reverseMap.has(serialized)) {
                const id = this.reverseMap.get(serialized)!;
                return id;
            } else return this.allocateTypeNode(t);
        }
        return ["object", "function"].includes(ty.kind) ? helper(ty) : this.allocateTypeNode(ty);
    }

    get(typeId: TypeId) {
        return typeId < this.typeNodes.length ? this.typeNodes[typeId] : undefined;
    }

    merge(tys: TypeId[]): TypeId {
        let tyList: TypeId[] = [], ret: TypeId, has_unknown = false, arrList = [];
        const tmp = tys.map(ty => { const typeNode = this.get(ty); return typeNode?.kind === "union" ? [...typeNode.types] : [ty] }).flat();
        const set = new Set(tmp.filter(ty => ty !== this.UNKNOWN));
        if (tmp.includes(this.UNKNOWN)) {
            // 保护，存在unknown就不推导Literal
            has_unknown = true;
            if (DEDUCE_ONLY_WHEN_ALL_KNOWNN) return this.UNKNOWN;
        }
        for (const ty of set) {
            const typeNode = this.get(ty);
            let cand = ty;
            if (typeNode?.kind === "literal" && (set.size > 1 || has_unknown)) {
                if (typeNode.value === undefined) {
                    cand = this.UNDEFINED;
                } else if (typeNode.value !== null) {
                    cand = typeof typeNode.value === "number" ? this.NUMBER : typeof typeNode.value === "string" ? this.STRING : this.BOOLEAN;
                }
            }
            if (typeNode?.kind === "array") {
                arrList.push(cand);
                continue;
            }
            tyList.push(cand);
        }
        if (arrList.length > 1) arrList = [this.newTypeNode({ kind: "array", elementType: this.ANY })];
        tyList = [...new Set(tyList), ...arrList]; // 去重

        if (tyList.length === 1) {
            ret = tyList[0];
        } else if (tyList.length > 1) {
            ret = this.newTypeNode({ kind: "union", types: tyList });
        } else {
            // console.warn(`Trap!!! merge types ${[...tys]} to UNKNOWN`);
            ret = this.UNKNOWN;
        }
        if (LOG_TYPE_FLOW)
            console.log(`merge types ${[...tys]} to ${ret}`);
        return ret;
    }

    // 序列化 TypeNode 为字符串, 确保唯一性
    private serialize(t: nType): string {
        if (!t) {
            console.warn(`illegal typeNode ${JSON.stringify(t)}`);
            return "illegal typeNode";
        }
        if (this.hash.has(t)) return this.hash.get(t)!;
        let ret;
        switch (t.kind) {
            case "primitive":
                ret = `primitive:${t.name}`;
                break;
            case "literal":
                ret = `literal:${typeof t.value}:${t.value}`;
                break;
            case "array":
                ret = `array:${t.elementType}`;
                break;
            case "function":
                ret = `function${t.id}:${Object.entries(t.param).sort().map(([idx, {id, type}]) => `${idx}:${id}:${type}`).join(",")}->${t.returnType}`;
                break;
            case "union":
                // 仅用排序副本生成哈希；不能改变类型节点的展示顺序。
                ret = `union:${[...t.types].sort().join("|")}`;
                break;
            case "object":
                ret = `object:{${t.id}:${Object.entries(t.properties).sort().map(([k, v]) => `${k}:${v}`).join(",")}}`;
                break;
            case "enum":
                ret = `enum:{${t.name}:${Object.entries(t.members).sort().map(([k, v]) => `${k}=${v}`).join(",")}}`;
        }
        this.hash.set(t, ret);
        return ret;
    }

    // 打印完整类型
    printFullType(n: TypeId): string {
        const occur: Record<string, TypeId> = {};
        const visited = new Set<TypeId>();
        return helper(this.typeNodes, n);
        function helper(typeNodes: nType[], n: TypeId): string {
            if (visited.has(n)) {
                return `<cyclic #${n}>`;
            }
            visited.add(n);

            const t = typeNodes[n];
            if (!t) {
                // if (LOG_TYPENODE)
                console.warn(`Type ID ${n} not found in typeNodes`);
                visited.delete(n);
                return "impossible! type unknown in printFullType";
            }
            let result: string;
            switch (t.kind) {
                case "primitive":
                    result = t.name;
                    break;
                case "literal":
                    result = `literal:${t.value}`;
                    break;
                case "array":
                    result = helper(typeNodes, t.elementType) + "[]";
                    break;
                case "function":
                    if (occur[t.id]) {
                        result = `function:${t.name}`;
                        break;
                    }
                    occur[t.id] = n;
                    // 构建参数列表
                    const paramIndices = Object.keys(t.param).map(Number).sort();
                    const paramsStr = paramIndices.map(idx => {
                        const paramInfo = t.param[idx];
                        const paramName = meta.paramName.get(paramInfo.id) || `param_${idx}`;
                        const paramType = helper(typeNodes, paramInfo.type);
                        return `${paramName}: ${paramType}`;
                    }).join(", ");
                    result = `(${paramsStr}) => ${helper(typeNodes, t.returnType)}`;
                    break;
                case "object":
                    if (occur[t.id]) {
                        result = `object:${t.name}`;
                        break;
                    }
                    occur[t.id] = n;
                    const propsStr = Object.entries(t.properties)
                        .map(([k, v]) => `${k}: ${helper(typeNodes, v)}`)
                        .join("; ");
                    result = `{ ${t.name} | ${propsStr} }`;
                    break;
                case "union":
                    result = t.types.map(ty => helper(typeNodes, ty)).join(" || ");
                    break;
                case "enum":
                    result = `enum ${t.name} { ${Object.entries(t.members).sort().map(([k, v]) => `${k}=${v}`).join(",")} }`;
                    break;
            }
            visited.delete(n);
            return result;
        }
    }

    printJsonType(typeId: TypeId): any {
        const visited = new Set<TypeId>();
        const occur: Record<number, TypeId> = {}; // 通过变量 ID 检测循环引用
        const helper = (id: TypeId): any => {
            if (visited.has(id)) {
                return `<cyclic #${id}>`;
            }
            visited.add(id);
            const t = this.typeNodes[id];
            if (!t) {
                visited.delete(id);
                return { kind: "unknown", id };
            }
            let result: any;
            switch (t.kind) {
                case "primitive":
                    result = { kind: "primitive", name: t.name };
                    break;
                case "literal":
                    result = typeof t.value === "bigint"
                        ? { kind: "literal", value: `${t.value}n`, valueKind: "bigint" }
                        : { kind: "literal", value: t.value };
                    break;
                case "array":
                    result = { kind: "array", elementType: helper(t.elementType) };
                    break;
                case "function":
                    if (occur[t.id]) {
                        result = `function:${t.name}`;
                        break;
                    }
                    occur[t.id] = id;
                    const params: any[] = [];
                    const paramIndices = Object.keys(t.param).map(Number).sort();
                    for (const idx of paramIndices) {
                        const paramInfo = t.param[idx];
                        params.push({
                            name: meta.paramName.get(paramInfo.id) || `param_${idx}`,
                            type: helper(paramInfo.type)
                        });
                    }
                    result = {
                        kind: "function",
                        name: t.name,
                        id: t.id,
                        params,
                        returnType: helper(t.returnType)
                    };
                    break;
                case "union":
                    result = { kind: "union", types: t.types.map(ty => helper(ty)) };
                    break;
                case "object":
                    if (occur[t.id]) {
                        result = `object:${t.name}`;
                        break;
                    }
                    occur[t.id] = id;
                    const properties: Record<string, any> = {};
                    for (const [key, propTypeId] of Object.entries(t.properties)) {
                        properties[key] = helper(propTypeId);
                    }
                    result = {
                        kind: "object",
                        name: t.name,
                        properties
                    };
                    break;
                case "enum":
                    const members: Record<string, any> = {};
                    for (const [key, memberTypeId] of Object.entries(t.members)) {
                        members[key] = helper(memberTypeId);
                    }
                    result = {
                        kind: "enum",
                        name: t.name,
                        members
                    };
                    break;
                default:
                    console.warn(`Unknown kind in printJsonType: ${(t as any).kind}`);
                    result = { kind: "unknown", id };
                    break;
            }
            visited.delete(id);
            return result;
        };
        return helper(typeId);
    }

    printAnnoType(typeId: TypeId): any {
        const node = this.typeNodes[typeId];
        if (!node) return "unknown";
      
        switch (node.kind) {
          case "primitive":
            return node.name;
          case "literal":
            return (typeof node.value) + " constant";
          case "union":
            return Array.from(new Set(node.types.map(t => this.printAnnoType(t))));
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

    /** 将 ground truth/feedback 类型转换为内部类型；无法完整表达时返回 UNKNOWN。 */
    parseTypeString(raw: string, options: { allowOpaqueGenerics?: boolean } = {}): TypeId | null {
        // TypeScript 没有独立解析 TypeNode 的公开入口，放进返回类型可复用完整类型语法。
        // 同时要求文件中只有这一条声明，避免 raw 用分号追加其他语句后仍被部分接受。
        const sourceFile = ts.createSourceFile(
            "__ast2type_type.ts",
            `declare function __Ast2TypeInput(): ${raw};`,
            ts.ScriptTarget.Latest,
            true,
            ts.ScriptKind.TS,
        );
        const diagnostics = (sourceFile as ts.SourceFile & {
            parseDiagnostics?: readonly ts.Diagnostic[];
        }).parseDiagnostics ?? [];
        const statements = sourceFile.statements.filter(statement => !ts.isEmptyStatement(statement));
        if (diagnostics.length > 0
            || statements.length !== 1
            || !ts.isFunctionDeclaration(statements[0])
            || statements[0].type === undefined) {
            return this.UNKNOWN;
        }

        const previous = this.allowOpaqueGenerics;
        this.allowOpaqueGenerics = options.allowOpaqueGenerics === true;
        try {
            return this._fromTypeScriptType(statements[0].type) ?? this.UNKNOWN;
        } finally {
            this.allowOpaqueGenerics = previous;
        }
    }

    /** null 表示内部模型无法无损表达；真正的 TypeScript unknown 返回 UNKNOWN TypeId。 */
    private _fromTypeScriptType(node: ts.TypeNode): TypeId | null {
        switch (node.kind) {
            case ts.SyntaxKind.AnyKeyword: return this.ANY;
            case ts.SyntaxKind.UnknownKeyword: return this.UNKNOWN;
            case ts.SyntaxKind.NumberKeyword: return this.NUMBER;
            case ts.SyntaxKind.StringKeyword: return this.STRING;
            case ts.SyntaxKind.BooleanKeyword: return this.BOOLEAN;
            case ts.SyntaxKind.UndefinedKeyword: return this.UNDEFINED;
            case ts.SyntaxKind.VoidKeyword: return this.VOID;
            case ts.SyntaxKind.NeverKeyword: return null;
            case ts.SyntaxKind.ObjectKeyword:
                return this.newTypeNode({
                    kind: "object", name: "object", id: ++this._synthObjId, properties: {},
                });
        }

        if (ts.isParenthesizedTypeNode(node)) return this._fromTypeScriptType(node.type);

        if (ts.isLiteralTypeNode(node)) {
            const literal = node.literal;
            if (ts.isStringLiteral(literal)) {
                return this.newTypeNode({ kind: "literal", value: literal.text });
            }
            if (ts.isNumericLiteral(literal)) {
                return this.newTypeNode({ kind: "literal", value: Number(literal.text) });
            }
            if (literal.kind === ts.SyntaxKind.TrueKeyword) {
                return this.newTypeNode({ kind: "literal", value: true });
            }
            if (literal.kind === ts.SyntaxKind.FalseKeyword) {
                return this.newTypeNode({ kind: "literal", value: false });
            }
            if (literal.kind === ts.SyntaxKind.NullKeyword) {
                return this.newTypeNode({ kind: "literal", value: null });
            }
            if (ts.isPrefixUnaryExpression(literal)
                && literal.operator === ts.SyntaxKind.MinusToken
                && ts.isNumericLiteral(literal.operand)) {
                return this.newTypeNode({ kind: "literal", value: -Number(literal.operand.text) });
            }
            return null;
        }

        if (ts.isTypePredicateNode(node)) {
            // 内部模型不记录谓词目标，但其运行时返回值仍可准确表示为 boolean。
            return node.assertsModifier ? null : this.BOOLEAN;
        }

        if (ts.isArrayTypeNode(node)) {
            const elementType = this._fromTypeScriptType(node.elementType);
            return elementType === null
                ? null
                : this.newTypeNode({ kind: "array", elementType });
        }

        if (ts.isTupleTypeNode(node)) {
            // 内部没有 tuple 节点，保守降为“所有元素类型的数组”；可选元素补 undefined。
            const elementTypes: TypeId[] = [];
            for (const rawElement of node.elements) {
                let element: ts.TypeNode = rawElement;
                let optional = false;
                let rest = false;
                if (ts.isNamedTupleMember(element)) {
                    optional = element.questionToken !== undefined;
                    rest = element.dotDotDotToken !== undefined;
                    element = element.type;
                } else if (ts.isOptionalTypeNode(element)) {
                    optional = true;
                    element = element.type;
                } else if (ts.isRestTypeNode(element)) {
                    rest = true;
                    element = element.type;
                }

                let elementType: TypeId | null;
                if (rest && ts.isArrayTypeNode(element)) {
                    elementType = this._fromTypeScriptType(element.elementType);
                } else {
                    elementType = this._fromTypeScriptType(element);
                }
                if (elementType === null) return null;
                elementTypes.push(elementType);
                if (optional) elementTypes.push(this.UNDEFINED);
            }
            const elementType = this._unionType(elementTypes);
            return this.newTypeNode({ kind: "array", elementType });
        }

        if (ts.isFunctionTypeNode(node)) {
            return this._signatureType(node.parameters, node.type, node.typeParameters);
        }

        // 当前内部模型无法区分普通函数和构造器，不能把构造器误当成实例或普通函数。
        if (ts.isConstructorTypeNode(node)) return null;

        if (ts.isUnionTypeNode(node)) {
            const types: TypeId[] = [];
            for (const member of node.types) {
                const type = this._fromTypeScriptType(member);
                // 不丢弃无法表达的分支，否则会把 GT 缩窄成一个错误但可比较的类型。
                if (type === null) return null;
                types.push(type);
            }
            return this._unionType(types);
        }

        if (ts.isTypeLiteralNode(node)) {
            const properties: Record<string, TypeId> = {};
            for (const member of node.members) {
                if (ts.isPropertySignature(member)) {
                    const name = member.name ? this._propertyName(member.name) : null;
                    // 重复成员可能是重载；单值属性表无法无损表示。
                    if (name === null || Object.prototype.hasOwnProperty.call(properties, name)) {
                        return null;
                    }
                    let type = member.type ? this._fromTypeScriptType(member.type) : this.ANY;
                    if (type === null) return null;
                    if (member.questionToken) type = this._unionType([type, this.UNDEFINED]);
                    properties[name] = type;
                    continue;
                }
                if (ts.isMethodSignature(member)) {
                    const name = member.name ? this._propertyName(member.name) : null;
                    if (name === null || Object.prototype.hasOwnProperty.call(properties, name)) {
                        return null;
                    }
                    let type = this._signatureType(
                        member.parameters,
                        member.type,
                        member.typeParameters,
                    );
                    if (type === null) return null;
                    if (member.questionToken) type = this._unionType([type, this.UNDEFINED]);
                    properties[name] = type;
                    continue;
                }
                return null;
            }
            return this.newTypeNode({
                kind: "object", name: "", id: ++this._synthObjId, properties,
            });
        }

        if (ts.isTypeReferenceNode(node)) {
            const name = this._entityName(node.typeName);
            if (name === null) return null;
            const typeArguments = node.typeArguments ?? [];
            // 数组是内部唯一能保留类型实参语义的泛型；其余泛型不能只擦掉实参。
            if ((name === "Array" || name === "ReadonlyArray") && typeArguments.length === 1) {
                const elementType = this._fromTypeScriptType(typeArguments[0]);
                return elementType === null
                    ? null
                    : this.newTypeNode({ kind: "array", elementType });
            }
            if (typeArguments.length > 0) {
                if (!this.allowOpaqueGenerics) return null;
                // 保留合法的泛型文本，避免 Agent 给出的 Record/Map/Promise 等类型被丢弃。
                return this.newTypeNode({
                    kind: "object", name: node.getText(), id: ++this._synthObjId, properties: {},
                });
            }
            return this.newTypeNode({
                kind: "object", name, id: ++this._synthObjId, properties: {},
            });
        }

        if (ts.isTypeOperatorNode(node)) {
            // createSourceFile 不做 grammar checking；readonly string 也会产生 AST，需显式拒绝。
            if (node.operator !== ts.SyntaxKind.ReadonlyKeyword
                || (!ts.isArrayTypeNode(node.type) && !ts.isTupleTypeNode(node.type))) {
                return null;
            }
            return this._fromTypeScriptType(node.type);
        }

        return null;
    }

    private _signatureType(
        parameters: readonly ts.ParameterDeclaration[],
        returnTypeNode: ts.TypeNode | undefined,
        typeParameters: readonly ts.TypeParameterDeclaration[] | undefined,
    ): TypeId | null {
        // 内部函数类型只有固定位置参数，不能表达泛型、默认值、receiver 或 rest 语义。
        if (typeParameters && typeParameters.length > 0) return null;
        const returnType = returnTypeNode ? this._fromTypeScriptType(returnTypeNode) : this.ANY;
        if (returnType === null) return null;
        const params: Record<number, { id: number; type: number }> = {};
        for (let index = 0; index < parameters.length; index++) {
            const parameter = parameters[index];
            if (parameter.initializer
                || parameter.dotDotDotToken
                || (parameter.modifiers && parameter.modifiers.length > 0)
                || (ts.isIdentifier(parameter.name) && parameter.name.text === "this")) {
                return null;
            }
            let type = parameter.type ? this._fromTypeScriptType(parameter.type) : this.ANY;
            if (type === null) return null;
            if (parameter.questionToken) type = this._unionType([type, this.UNDEFINED]);
            params[index] = { id: -(++this._synthObjId), type };
        }
        return this.newTypeNode({
            kind: "function", name: "", id: ++this._synthObjId,
            param: params, returnType,
        });
    }

    private _unionType(types: TypeId[]): TypeId {
        // unknown/any 在 TS 联合中的支配关系不能靠丢弃成员近似。
        if (types.length === 0 || types.includes(this.UNKNOWN)) return this.UNKNOWN;
        if (types.includes(this.ANY)) return this.ANY;
        const uniqueTypes = [...new Set(types)];
        return uniqueTypes.length === 1
            ? uniqueTypes[0]
            : this.newTypeNode({ kind: "union", types: uniqueTypes });
    }

    private _entityName(name: ts.EntityName): string | null {
        if (ts.isIdentifier(name)) return name.text;
        const left = this._entityName(name.left);
        return left === null ? null : `${left}.${name.right.text}`;
    }

    private _propertyName(name: ts.PropertyName): string | null {
        if (ts.isIdentifier(name) || ts.isStringLiteral(name) || ts.isNumericLiteral(name)) {
            // The internal property maps use ordinary objects, where this key has setter semantics.
            return name.text === "__proto__" ? null : name.text;
        }
        return null;
    }
}

type TypeId = number;

// Type 类型结构体
export type nType =
    | { kind: "primitive"; name: string }
    | { kind: "literal"; value: string | number | boolean | RegExp | bigint | null }
    | { kind: "array"; elementType: number }
    | { kind: "function"; name: string; id: number; param: Record<number, {id: number; type: number}>; returnType: number }
    | { kind: "union"; types: number[] }
    | { kind: "object"; name: string; id: number; properties: Record<string, number> }
    | { kind: "enum"; name: string; members: Record<string, number> };


export interface NodeState {
    val: any      // 不同 Strategy 决定 val 的含义
    addProperty(prop: string, ns: NodeState): boolean
    getProperty(prop: string): NodeState | null
    addElement(ns: NodeState): boolean
    getElement(): NodeState | null
    addParam(paramId: VarId, paramType: NodeState): boolean
    getParam(paramId: VarId): NodeState | null
    addReturnType(returnType: NodeState): boolean
    getReturnType(): NodeState | null
    getFuncVaridorNull(): VarId | null
    equals(other: NodeState): boolean
    toString(): string
    toJson(): any
    toAnno(): any

}

export class DeterminantNodeState implements NodeState {
    val: TypeId;

    constructor(val: TypeId) {
        tNode.type2state.set(val, (tNode.type2state.get(val) || new Set<NodeState>()).add(this));
        this.val = val;
    }

    addProperty(prop: string, ns: NodeState) { 
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to add property to undefined typeid: ${this.val}`);
            return false;
        }
        if (typeNode.kind !== "object") {
            console.warn(`Trying to add property to non-object type: ${tNode.printFullType(this.val)}`);
            return false;
        }
        if (typeNode.properties[prop] === ns.val) {
            // 属性已存在且类型相同，无需修改
            return false;
        }
        typeNode.properties[prop] = ns.val;
        tNode.modifyTypeNode(this.val, typeNode);
        return true;
    }

    getProperty(prop: string): NodeState | null {
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to get property from undefined typeidd: ${this.val}`);
            return null;
        }   
        if (typeNode.kind !== "object") {
            console.warn(`Trying to get property from non-object type: ${tNode.printFullType(this.val)}`);
            return null;
        }
        const propTypeId = typeNode.properties[prop];   
        if (propTypeId === undefined) {
            return null;
        }
        return new DeterminantNodeState(propTypeId);
    }

    addElement(ns: NodeState): boolean {
        const oldTypeNode = tNode.get(this.val);
        if (!oldTypeNode) {
            console.warn(`Trying to add element to undefined typeid: ${this.val}`);
            return false;
        }
        if (oldTypeNode.kind !== "array") {
            console.warn(`Trying to add element to non-array type: ${tNode.printFullType(this.val)}`);
            return false;
        }
        if (oldTypeNode.elementType === ns.val) {
            // 元素类型已相同，无需修改
            return false;
        }
        // 不修改共享的 oldTypeNode，创建全新 array 类型
        const newElementType = tNode.merge([oldTypeNode.elementType, ns.val]);
        this.val = tNode.newTypeNode({ kind: "array", elementType: newElementType });
        return true;
    }

    getElement(): NodeState | null {
        const typeNode = tNode.get(this.val);   
        if (!typeNode) {
            console.warn(`Trying to get element from undefined typeid: ${this.val}`);
            return null;
        }
        if (typeNode.kind !== "array") {
            console.warn(`Trying to get element from non-array type: ${tNode.printFullType(this.val)}`);
            return null;
        }
        return new DeterminantNodeState(typeNode.elementType);
    }

    addParam(paramId: VarId, paramType: NodeState): boolean {
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to add param to undefined typeid: ${this.val}`);
            return false;
        }
        if (typeNode.kind !== "function") {
            console.warn(`Trying to add param to non-function type: ${tNode.printFullType(this.val)}`);
            return false;
        }

        // 从meta获取参数索引
        const paramIndex = meta.paramIndex.get(paramId);
        if (paramIndex === undefined) {
            console.warn(`Parameter index not found for paramId: ${paramId}`);
            return false;
        }

        // 检查是否已存在该索引的参数
        if (paramIndex in typeNode.param) {
            // 更新现有参数类型
            if (typeNode.param[paramIndex].type === paramType.val) {
                return false; // 类型相同，无需修改
            }
            typeNode.param[paramIndex] = { id: paramId, type: paramType.val };
        } else {
            // 添加新参数
            typeNode.param[paramIndex] = { id: paramId, type: paramType.val };
        }

        tNode.modifyTypeNode(this.val, typeNode);
        return true;
    }

    getParam(paramId: VarId): NodeState | null {
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to get param from undefined typeid: ${this.val}`);
            return null;
        }
        if (typeNode.kind !== "function") {
            console.warn(`Trying to get param from non-function type: ${tNode.printFullType(this.val)}`);
            return null;
        }

        // 从meta获取参数索引，然后查找
        const paramIndex = meta.paramIndex.get(paramId);
        if (paramIndex === undefined) {
            return null;
        }

        const paramInfo = typeNode.param[paramIndex];
        if (!paramInfo || paramInfo.id !== paramId) {
            return null;
        }

        return new DeterminantNodeState(paramInfo.type);
    }

    addReturnType(returnType: NodeState): boolean {
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to add return type on undefined typeid: ${this.val}`);
            return false;
        }
        if (typeNode.kind !== "function") {
            console.warn(`Trying to add return type on non-function type: ${tNode.printFullType(this.val)}`);
            return false;
        }

        const oldReturnType = typeNode.returnType;
        const newReturnType = tNode.merge([oldReturnType, returnType.val]);

        if (oldReturnType === newReturnType) {
            return false; // 返回类型未改变
        }

        typeNode.returnType = newReturnType;
        tNode.modifyTypeNode(this.val, typeNode);
        return true;
    }

    getReturnType(): NodeState | null {
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to get return type from undefined typeid: ${this.val}`);
            return null;
        }
        if (typeNode.kind !== "function") {
            console.warn(`Trying to get return type from non-function type: ${tNode.printFullType(this.val)}`);
            return null;
        }
        return new DeterminantNodeState(typeNode.returnType);
    }

    // static merge(tys: DeterminantNodeState[]): DeterminantNodeState {
    //     const typeIds = tys.map(t => t.val);
    //     const mergedTypeId = tNode.merge(typeIds);
    //     return new DeterminantNodeState(mergedTypeId);
    // }

    getFuncVaridorNull(): VarId | null {
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to get func varId from undefined typeid: ${this.val}`);
            return null;
        }
        if (typeNode.kind !== "function") {
            console.warn(`Trying to get func varId from non-function type: ${tNode.printFullType(this.val)}`);
            return null;
        }
        return typeNode.id ?? null;
    }

    equals(other: NodeState): boolean {
        const detNode = other as DeterminantNodeState;
        return this.val === detNode?.val;
    }

    toString(): string {
        return tNode.printFullType(this.val);
    }

    toJson() {
        return tNode.printJsonType(this.val);
    }

    toAnno(): any {
        return tNode.printAnnoType(this.val);
    }
}
