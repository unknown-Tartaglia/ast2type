import { solver, tNode } from "../ast2type"
import { TypeId, VarId } from "./fact"
import { TypeGraph } from "./graph"
import { DeterminantNodeState, NodeState } from "./nType"

export interface Strategy {
    newNodeState(typeId: TypeId): NodeState 
    propagate(nodeId: VarId, graph: TypeGraph): VarId[]
    merge(nodeId: VarId, graph: TypeGraph): NodeState
    result(graph: TypeGraph): any
}

export class DeterminantStrategy implements Strategy {
    newNodeState(typeId: TypeId) {
        return new DeterminantNodeState(typeId);
    }

    propagate(nodeId: VarId, graph: TypeGraph) {
        const worklist: VarId[] = [];
        const fromType = graph.nodes.get(nodeId);
        if (fromType === undefined) return worklist;
        for (const edge of Array.from(graph.toEdges.get(nodeId) ?? []).filter(e =>
            e.type === "sameType" || e.type === "ArgToParam" || e.type === "assignment")) {
            // 简单的类型传播：将 nodeId 的类型传播到 edge.to
            let propagated = fromType;
            if (edge.type === "assignment") {
                const type = tNode.get(fromType.val);
                if (type?.kind === "literal" && type.value !== null) {
                    const primitive = typeof type.value === "number"
                        ? tNode.NUMBER
                        : typeof type.value === "string"
                            ? tNode.STRING
                            : typeof type.value === "boolean"
                                ? tNode.BOOLEAN
                                : undefined;
                    if (primitive !== undefined) propagated = this.newNodeState(primitive);
                }
            }
            graph.setSrcType(edge, propagated);
            const toNode = edge.to;
            const toType = graph.nodes.get(toNode);
            const newType = this.merge(toNode, graph);
            if (!newType.equals(toType as DeterminantNodeState)) {
                graph.setType(toNode, newType);
                worklist.push(toNode);
            }
        }
        return worklist;
    }

    merge(nodeId: VarId, graph: TypeGraph) {
        const edges = Array.from(graph.getFromEdges(nodeId)).filter(e =>
            e.type === "sameType" || e.type === "ArgToParam" || e.type === "assignment");
        const mergedTypeIds = new Set<TypeId>();
        // 保留当前类型，防止 extend 的加宽被 sameType 覆盖回窄类型（排除 any/unknown）
        const cur = graph.nodes.get(nodeId);
        if (cur && cur.val !== tNode.ANY && cur.val !== tNode.UNKNOWN) {
            mergedTypeIds.add(cur.val);
        }
        for (const edge of edges)
            if (edge.cand) {
                mergedTypeIds.add(edge.cand.val);
            }
        const ret = tNode.merge(Array.from(mergedTypeIds));
        return new DeterminantNodeState(ret);
    }

    result(graph: TypeGraph) {
        
    }
}
