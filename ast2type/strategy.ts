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
        for (const edge of Array.from(graph.toEdges.get(nodeId) ?? []).filter(e => e.type === "sameType")) {
            // 简单的类型传播：将 nodeId 的类型传播到 edge.to
            graph.setSrcType(edge, fromType);
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
        // 简单的合并策略：取所有合并节点的类型的并集
        const edges = Array.from(graph.getFromEdges(nodeId)).filter(e => e.type === "sameType");
        const mergedTypes = new Set<NodeState>();
        for (const edge of edges)
            if (edge.cand) {
                mergedTypes.add(edge.cand);
            }
        const ret = tNode.merge(Array.from(mergedTypes).map(t => t.val));
        return new DeterminantNodeState(ret);
    }

    result(graph: TypeGraph) {
        
    }
}