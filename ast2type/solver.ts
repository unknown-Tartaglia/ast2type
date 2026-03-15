import path from "path";
import * as fs from "fs";
import { meta, outputDir, tNode } from "../ast2type";
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
            if (effect.kind === "delayEdge") {
                this.graph.addDelayedEdge(effect.from, effect.toFuncVarId, effect.argIdx, effect.edgeType);
            }
        }   
        for (const effect of effects) {
            if (effect.kind === "addEdge") {
                this.graph.addEdge(effect.from, effect.to, effect.edgeType);
            } else if (effect.kind === "genType") {
                this.graph.setType(effect.node, this.strategy.newNodeState(effect.type));
                this.worklist.push(effect.node);
            }
        }
        for (const effect of effects) {
            if (effect.kind === "setVoid") {
                this.graph.setRetType(effect.node, tNode.VOID);
            }
        }   
        for (const effect of effects) {
            if (effect.kind === "mergeNode") {
                this.graph.mergeNodes(effect.source, effect.target);
            }
        }

        // 使用策略进行传播
        let iteration = 0;
        const maxIterations = 1000000;
        while (this.worklist.length > 0) {
            iteration++;
            if (iteration > maxIterations) {
                console.error(`Solver exceeded maximum iterations (${maxIterations}), possible infinite loop`);
                break;
            }
            const nodeId = this.worklist.shift()!;
            let worklist;
            worklist = this.strategy.propagate(nodeId, this.graph);
            this.worklist.push(...worklist);
            worklist = this.graph.extend(nodeId);
            this.worklist.push(...worklist);
        }
        if (iteration > maxIterations) {
            console.error("Solver terminated due to possible infinite loop");
        }
    }

    output(): any {
        fs.mkdirSync(outputDir, { recursive: true });

        // 写出类型图（仅 JSON）
        const jsonGraph = this.graph.toJson();
        const jsonOut = path.join(outputDir, "typegraph.json");
        writeJsonStream(jsonOut, jsonGraph);

        // 写出类型标注
        const anno = this.graph.toAnno();
        const annoOut = path.join(outputDir, "typeinfo.json");
        writeJsonStream(annoOut, anno);

        // 按 file 分组
        const groups : Record<string, any> = {};
        for (const item of anno) {
            if (!groups[item.relapath]) groups[item.relapath] = [];
            const { file, relapath, ...rest } = item;  // 去掉 file 字段
            groups[item.relapath].push(rest);
        }

        for (const file in groups) {
            const outfile = path.join(path.join(outputDir, "typeinfo"), file + ".json");
            fs.mkdirSync(path.dirname(outfile), { recursive: true }); // 创建目录
            writeJsonStream(outfile, groups[file]);
        }

        // 评估标注
        const evalResult = this.graph.evaluate();
        const evalOut = path.join(outputDir, "evaluation.json");
        writeJsonStream(evalOut, evalResult);

        console.log(`Done. Output written to ${outputDir}`);
    }
}

