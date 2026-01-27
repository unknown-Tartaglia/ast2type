import { DEDUCE_ONLY_WHEN_ALL_KNOWNN, LOG_TYPE_FLOW, LOG_TYPENODE, LOG_TYPENODE_VERBOSE, solver, tNode } from "../ast2type";
import { VarId } from "./fact";

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

    constructor() {
        // 预定义一些基础类型
        this.typeNodes.push({ kind: "primitive", name: "any" });    // 0: any
        this.typeNodes.push({ kind: "primitive", name: "unknown" }); // 1: unknown
        this.typeNodes.push({ kind: "primitive", name: "number" });  // 2: number
        this.typeNodes.push({ kind: "primitive", name: "string" });  // 3: string
        this.typeNodes.push({ kind: "primitive", name: "boolean" }); // 4: boolean
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
                console.log(`TypeNode ${node} affected by modification of TypeId ${id}, added to worklist`);
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
                        occur.set(t.id, this.newTypeNode(t));
                        return occur.get(t.id)!;
                    }
                    occur.set(t.id, this.UNKNOWN);

                    t.returnType = helper(this.typeNodes[t.returnType]);

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
                        occur.set(t.id, this.newTypeNode(t));
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
            if (typeNode?.kind === "literal" && (set.size > 1 || has_unknown)) cand = typeof typeNode.value === "number" ? this.NUMBER : typeof typeNode.value === "string" ? this.STRING : this.BOOLEAN;
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
                ret = `literal:${t.value}`;
                break;
            case "array":
                ret = `array:${t.elementType}`;
                break;
            case "function":
                ret = `function${t.id}->${t.returnType}`;
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
        this.hash.set(t, ret);
        return ret;
    }

    // 打印完整类型
    printFullType(n: TypeId): string {
        const occur: Record<string, TypeId> = {};
        return helper(this.typeNodes, n);
        function helper(typeNodes: nType[], n: TypeId): string {
            const t = typeNodes[n];
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
                    return helper(typeNodes, t.elementType) + "[]";
                case "function":
                    if (occur[t.id]) {
                        return `function:${t.name}`;
                    }
                    occur[t.id] = n;

                    return `() => ${helper(typeNodes, t.returnType)}`;
                case "object":
                    if (occur[t.id]) {
                        return `object:${t.name}`;
                    }
                    occur[t.id] = n;
                    const propsStr = Object.entries(t.properties)
                        .map(([k, v]) => `${k}: ${helper(typeNodes, v)}`)
                        .join("; ");
                    return `{ ${t.name} | ${propsStr} }`;
                case "union":
                    return t.types.map(ty => helper(typeNodes, ty)).join(" | ");
                case "enum":
                    return `enum ${t.name} { ${Object.entries(t.members).sort().map(([k, v]) => `${k}=${v}`).join(",")} }`;
            }
        }
    }
}

type TypeId = number;

// Type 类型结构体
export type nType =
    | { kind: "primitive"; name: string }
    | { kind: "literal"; value: string | number | boolean | RegExp | bigint | null }
    | { kind: "array"; elementType: number }
    | { kind: "function"; name: string; id: number; returnType: number }
    | { kind: "union"; types: number[] }
    | { kind: "object"; name: string; id: number; properties: Record<string, number> }
    | { kind: "enum"; name: string; members: Record<string, number> };


export interface NodeState {
    val: any      // 不同 Strategy 决定 val 的含义
    addProperty(prop: string, ns: NodeState): boolean
    getProperty(prop: string): NodeState | null
    addElement(ns: NodeState): boolean
    getElement(): NodeState | null
    toString(): string
    equals(other: NodeState): boolean
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
        const typeNode = tNode.get(this.val);
        if (!typeNode) {
            console.warn(`Trying to add element to undefined typeid: ${this.val}`);
            return false;
        }
        if (typeNode.kind !== "array") {
            console.warn(`Trying to add element to non-array type: ${tNode.printFullType(this.val)}`);
            return false;
        }
        if (typeNode.elementType === ns.val) {
            // 元素类型已相同，无需修改
            return false;
        }
        typeNode.elementType = tNode.merge([typeNode.elementType, ns.val]);
        this.val = tNode.newTypeNode(typeNode); // 重新注册类型节点
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

    // static merge(tys: DeterminantNodeState[]): DeterminantNodeState {
    //     const typeIds = tys.map(t => t.val);
    //     const mergedTypeId = tNode.merge(typeIds);
    //     return new DeterminantNodeState(mergedTypeId);
    // }
    equals(other: DeterminantNodeState): boolean {
        return this.val === other?.val;
    }

    toString(): string {
        return tNode.printFullType(this.val);
    }
}