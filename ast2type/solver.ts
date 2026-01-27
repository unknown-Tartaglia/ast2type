import path from "path";
import * as fs from "fs";
import { outputDir, tNode } from "../ast2type";
import { FactStore, TypeId, VarId } from "./fact"
import { TypeGraph } from "./graph"
import { Rule, RuleStore } from "./rule";
import { Strategy } from "./strategy"
import { writeJsonStream } from "../code2ast";

export class Solver {
    graph = new TypeGraph();
    worklist: VarId[] = []

    constructor(private rule: RuleStore, private strategy: Strategy) { }

    solve(facts: FactStore) {
        // 建图
        const effects = this.rule.applyRules(facts.facts);
        for (const effect of effects) {
            if (effect.kind === "addEdge") {
                this.graph.addEdge(effect.from, effect.to, effect.edgeType);
            } else if (effect.kind === "genType") {
                this.graph.setType(effect.node, this.strategy.newNodeState(effect.type));
                this.worklist.push(effect.node);
            }
        }
        for (const effect of effects) {
            if (effect.kind === "mergeNode") {
                this.graph.mergeNodes(effect.source, effect.target);
            }
        }

        // 使用策略进行传播
        while (this.worklist.length > 0) {
            const nodeId = this.worklist.shift()!;
            let worklist;
            worklist = this.strategy.propagate(nodeId, this.graph);
            this.worklist.push(...worklist);
            worklist = this.graph.extend(nodeId);
            this.worklist.push(...worklist);
        }
    }

    output(): any {
        const outDir = path.join(outputDir, "typegraph");
        fs.mkdirSync(outDir, { recursive: true });

        // 写出类型图（仅 JSON）
        const jsonGraph = this.graph.toJson();
        const jsonOut = path.join(outDir, "typegraph.json");
        writeJsonStream(jsonOut, jsonGraph);

        console.log(`Done. Output written to ${outDir}`);
    }
}

