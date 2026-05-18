import path from "path";
import * as fs from "fs";
import { injectFeedback, meta, outputDir, tNode } from "../ast2type";
import { Fact, FactStore, TypeId, VarId } from "./fact"
import { TypeGraph } from "./graph"
import { Rule, RuleStore } from "./rule";
import { Strategy } from "./strategy"
import { writeJsonStream } from "../code2ast";

export interface UnkSpot {
  id: number;
  context: string;
  exprText: string;
  exprKind: string;
  morphKind: string;
  location: number;
  pos: { line: number; column: number } | null;
  type: "unknown";
  relapath: string;
  file: string;
}

export class Solver {
    graph = new TypeGraph();
    worklist: VarId[] = []

    constructor(private rule: RuleStore, private strategy: Strategy) { }

    /** 收集图中节点未知信息，供 LLM Agent 推断 */
    getUnkInfo(): UnkSpot[] {
        const spots: UnkSpot[] = [];
        for (const [id, _] of  this.graph.toEdges) {
            if (!this.graph.nodes.has(id)  && this.graph.getFromEdges(id).size === 0) {
                let file = meta.file.get(id);
                let relapath = file ? file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "") : "unknown_relapath";
                file = file ? path.join(file.split("ast" + require("path").sep)[0].replace("_output", ""), file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "")) : "unknown_file";
                spots.push({
                    id: id,
                    context: meta.context.get(id) || "",
                    exprText: meta.text.get(id) || "",
                    exprKind: meta.v8Kind.get(id) || "",
                    morphKind: meta.kind.get(id) || "",
                    location: meta.offset.get(id) || -1,
                    pos: meta.pos.get(id) || null,
                    type: "unknown",
                    relapath: relapath,
                    file: file,
                });
            }
        }
        // for (const [id, kind] of meta.declKind) {
        //     const entry: UnkSpot = {
        //         id,
        //         identifier: meta.text.get(id) || "",
        //         kind,
        //         offset: meta.offset.get(id) ?? -1,
        //         pos: meta.pos.get(id) || null,
        //         file: "",
        //         context: meta.context.get(id) || "",
        //     };
        //     const fullPath = meta.file.get(id);
        //     if (fullPath) {
        //         const parts = fullPath.split("ast" + require("path").sep);
        //         entry.file = path.join(parts[0] || "", parts[1] || "")
        //             .replace(/\^/g, require("path").sep)
        //             .replace(/\.ast\.json$/, "");
        //     } else {
        //         entry.file = "unknown";
        //     }
        //     if (kind === "Parameter") {
        //         for (const [funcVarId, paramMap] of meta.funcParamMap) {
        //             for (const param of paramMap.values()) {
        //                 if (param === id) {
        //                     entry.function = meta.funcName.get(funcVarId) || "";
        //                     break;
        //                 }
        //             }
        //             if (entry.function) break;
        //         }
        //     }
        //     spots.push(entry);
        // }
        return spots;
    }

    /** 将 LLM 推断的类型注入为 Fact 并继续求解（增量，不清空已求结果） */
    injectFeedback(feedback: Array<{ id: number; type: string }>) {
        const primTypeMap: Record<string, number> = {
            number: tNode.NUMBER,
            string: tNode.STRING,
            boolean: tNode.BOOLEAN,
            void: tNode.VOID,
            any: tNode.ANY,
            undefined: tNode.UNDEFINED,
        };

        const newFacts: Fact[] = injectFeedback(feedback);

        if (newFacts.length === 0) return;

        // 对新 fact 跑规则 → 增量注入图
        const effects = this.rule.applyRules(newFacts);
        for (const effect of effects) {
            if (effect.kind === "genType") {
                this.graph.setType(
                    effect.node,
                    this.strategy.newNodeState(effect.type)
                );
                this.worklist.push(effect.node);
            } else if (effect.kind === "addEdge") {
                this.graph.addEdge(effect.from, effect.to, effect.edgeType);
                this.worklist.push(effect.to);
            }
        }

        // 继续推进
        let iteration = 0;
        const maxIterations = 1000000;
        while (this.worklist.length > 0) {
            iteration++;
            if (iteration > maxIterations) {
                console.error(
                    `[agent] Solver exceeded max iterations (${maxIterations})`
                );
                break;
            }
            const nodeId = this.worklist.shift()!;
            let wl = this.strategy.propagate(nodeId, this.graph);
            this.worklist.push(...wl);
            wl = this.graph.extend(nodeId);
            this.worklist.push(...wl);
        }
    }

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
        const [anno, unk] = this.graph.toAnno();
        const annoOut = path.join(outputDir, "typeinfo.json");
        writeJsonStream(annoOut, anno);
        const unkOut = path.join(outputDir, "unkinfo.json");
        writeJsonStream(unkOut, unk);

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

