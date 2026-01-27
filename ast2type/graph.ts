import { ConstructorTypeNode } from "ts-morph";
import { meta, solver, tNode } from "../ast2type";
import { VarId } from "./fact"
import { NodeState } from "./nType";

export class TypeGraph {
    nodes = new Map<VarId, NodeState>()
    state2node = new Map<NodeState, Set<VarId>>()
    toEdges = new Map<VarId, Set<Edge>>()
    fromEdges = new Map<VarId, Set<Edge>>()


    addEdge(from: VarId, to: VarId, type: string) {
        const edge = new Edge(from, to, type, null);

        if (!this.toEdges.has(from)) {
            this.toEdges.set(from, new Set<Edge>());
        }
        this.toEdges.get(from)!.add(edge);

        if (!this.fromEdges.has(to)) {
            this.fromEdges.set(to, new Set<Edge>());
        }
        this.fromEdges.get(to)!.add(edge);  
    }

    mergeNodes(source: VarId, target: VarId) {
        if (source === target) return;

        // 将 source 的所有边转移到 target
        for (const edge of this.getToEdges(source)) {
            edge.from = target;
            if (!this.toEdges.has(target)) {    
                this.toEdges.set(target, new Set<Edge>());
            }
            this.toEdges.get(target)!.add(edge);
        }
        for (const edge of this.getFromEdges(source)) {
            edge.to = target;
            if (!this.fromEdges.has(target)) {
                this.fromEdges.set(target, new Set<Edge>());
            }
            this.fromEdges.get(target)!.add(edge);  
        }

        // 删除 source 节点及其边
        this.toEdges.delete(source);
        this.fromEdges.delete(source);
        this.nodes.delete(source);
    }

    setType(node: VarId, val: NodeState) {
        const oldState = this.nodes.get(node);
        if (oldState) {
            this.state2node.get(oldState)?.delete(node);
        }
        this.nodes.set(node, val);
        this.state2node.set(val, (this.state2node.get(val) || new Set<VarId>()).add(node));
    }

    getToEdges(node: VarId): Set<Edge> {
        return this.toEdges.get(node) || new Set<Edge>();
    }

    getFromEdges(node: VarId): Set<Edge> {
        return this.fromEdges.get(node) || new Set<Edge>();
    }

    setSrcType(edge: Edge, val: NodeState) {
        edge.cand = val;
    }

    // 扩展节点，例如添加属性边等
    extend(nodeId: VarId) {
        const worklist : VarId[] = [];
        const ty = this.nodes.get(nodeId);
        if (!ty) return worklist;
        for (const edge of this.getFromEdges(nodeId)) {
            if (edge.type === "property") {
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                fromType.addProperty(meta.propName.get(nodeId)!, ty);
            }
            if (edge.type === "ArrayElement") { 
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                const changed = fromType.addElement(ty);
                if (changed) worklist.push(edge.from);
            }
        }
        for (const edge of this.getToEdges(nodeId)) {
            if (edge.type === "property") {
                const toType = this.nodes.get(edge.to);
                const newType = ty.getProperty(meta.propName.get(edge.to)!);
                if (!newType) continue;
                if (!toType || !toType.equals(newType)) {
                    this.setType(edge.to, newType);
                    worklist.push(edge.to);
                }
            }
            if (edge.type === "ArrayElement") {
                const toType = this.nodes.get(edge.to);
                const newType = ty.getElement();
                if (!newType) continue;
                if (!toType || !toType.equals(newType)) {
                    this.setType(edge.to, newType);
                    worklist.push(edge.to);
                }
            }
        }
        return worklist;
    }

    toJson() {
        const nodes: any[] = [];
        const edges: any[] = [];
        const unknownNodes: Set<VarId> = new Set<VarId>();
        for (const [nodeId, state] of this.nodes) {
            nodes.push({
                id: nodeId,
                label: meta.text.get(nodeId) || `var_${nodeId}`, 
                type: state.toString(),
                text: meta.text.get(nodeId) || "",
                file: meta.file.get(nodeId),
                position: meta.pos.get(nodeId),
              });
        }
        for (const [_, edgeSet] of this.toEdges) {
            for (const edge of edgeSet) {
                edges.push({
                    from: edge.from,
                    to: edge.to,
                    label: edge.type,
                });
                if (!this.nodes.has(edge.from)) unknownNodes.add(edge.from);
                if (!this.nodes.has(edge.to)) unknownNodes.add(edge.to);
            }
        }
        for (const unk of unknownNodes) {   
            nodes.push({
                id: unk,
                label: meta.text.get(unk) || `var_${unk}`,
                type: "unknown",
                text: meta.text.get(unk) || "",
                file: meta.file.get(unk),
                position: meta.pos.get(unk),
            });
        }
        return { nodes, edges };
    }
}


class Edge {
    from: VarId
    to: VarId
    type: string
    cand: NodeState | null
    constructor(from: VarId, to: VarId, type: string, cand: NodeState | null) {
        this.from = from;
        this.to = to;
        this.type = type;
        this.cand = cand;
    }
}

