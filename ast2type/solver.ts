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
  slot: AgentCandidateSlot;
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

export type AgentCandidateMode = "fair" | "gt";
export type AgentCandidateSlot = "value" | "return";

export interface AgentFeedbackEntry {
  id: number;
  type: string;
  slot?: AgentCandidateSlot;
}

const VALUE_DECLARATION_KINDS = new Set([
    "VariableDeclaration",
    "Parameter",
    "PropertyDeclaration",
    "PropertySignature",
]);

const FUNCTION_DECLARATION_KINDS = new Set([
    "FunctionDeclaration",
    "FunctionExpression",
    "ArrowFunction",
    "MethodSignature",
    "MethodDeclaration",
]);

export class Solver {
    graph = new TypeGraph();
    worklist: VarId[] = []

    constructor(private rule: RuleStore, private strategy: Strategy) { }

    private buildUnkSpot(id: VarId, slot: AgentCandidateSlot): UnkSpot {
        const astFile = meta.file.get(id);
        const marker = `ast${path.sep}`;
        const markerIndex = astFile?.lastIndexOf(marker) ?? -1;
        let relapath = "unknown_relapath";
        let file = "unknown_file";

        if (astFile && markerIndex >= 0) {
            relapath = astFile
                .slice(markerIndex + marker.length)
                .replace(/\^/g, path.sep)
                .replace(/\.ast\.json$/, "");
            file = path.join(
                astFile.slice(0, markerIndex).replace(/_output([/\\])$/, "$1"),
                relapath,
            );
        }

        return {
            id,
            slot,
            context: meta.context.get(id) || "",
            exprText: meta.text.get(id) || "",
            exprKind: meta.v8Kind.get(id) || "",
            morphKind: meta.kind.get(id) || "",
            location: meta.offset.get(id) ?? -1,
            pos: meta.pos.get(id) || null,
            type: "unknown",
            relapath,
            file,
        };
    }

    /**
     * 收集供 LLM Agent 推断的候选。
     *
     * fair: 从源码声明元数据枚举，不读取 annotation 边，因此候选不受 GT 影响。
     * gt: 保留历史图边算法，注入 GT 后新增的 annotation 边可以产生候选。
     */
    getUnkInfo(mode: AgentCandidateMode = "fair"): UnkSpot[] {
        const spots: UnkSpot[] = [];
        if (mode === "gt") {
            for (const [id] of this.graph.toEdges) {
                if (!this.graph.nodes.has(id) && this.graph.getFromEdges(id).size === 0) {
                    spots.push(this.buildUnkSpot(id, "value"));
                }
            }
            return spots;
        }

        const seen = new Set<string>();
        const addSpot = (id: VarId, slot: AgentCandidateSlot) => {
            const key = `${id}:${slot}`;
            if (seen.has(key)) return;
            seen.add(key);
            spots.push(this.buildUnkSpot(id, slot));
        };

        for (const [declarationId, kind] of meta.declKind) {
            if (VALUE_DECLARATION_KINDS.has(kind)) {
                const state = this.graph.nodes.get(declarationId);
                if (!state || state.val === tNode.UNKNOWN) {
                    addSpot(declarationId, "value");
                }
                continue;
            }

            if (!FUNCTION_DECLARATION_KINDS.has(kind)) continue;

            const functionId = meta.funcBindMap.get(declarationId) ?? declarationId;
            const state = this.graph.nodes.get(functionId) ?? this.graph.nodes.get(declarationId);
            if (!state) continue;
            const functionType = tNode.get(state.val);
            if (functionType?.kind === "function" && functionType.returnType === tNode.UNKNOWN) {
                addSpot(functionId, "return");
            }
        }

        return spots;
    }

    /** 将 LLM 推断的类型注入为 Fact 并继续求解（增量，不清空已求结果） */
    injectFeedback(feedback: AgentFeedbackEntry[]) {
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
            this.graph.traceEvent("propagate:before", nodeId);
            let wl = this.strategy.propagate(nodeId, this.graph);
            this.worklist.push(...wl);
            this.graph.traceAffected("propagate:affected", nodeId, wl);
            this.graph.traceEvent("propagate:after", nodeId);
            wl = this.graph.extend(nodeId);
            this.worklist.push(...wl);
            this.graph.traceAffected("extend:affected", nodeId, wl);
            this.graph.traceEvent("extend:after", nodeId);
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
        const visitCount = new Map<VarId, number>();
        while (this.worklist.length > 0) {
            iteration++;
            if (iteration > maxIterations) {
                console.error(`Solver exceeded maximum iterations (${maxIterations}), possible infinite loop`);
                // 诊断：找出被重复处理最多的节点
                const top = Array.from(visitCount.entries())
                    .sort((a, b) => b[1] - a[1]).slice(0, 10);
                console.error("Top 10 most-visited nodes:");
                for (const [id, count] of top) {
                    const t = this.graph.nodes.get(id);
                    const edgeTypes = Array.from(this.graph.getFromEdges(id))
                        .map(e => e.type).join(',');
                    console.error(`  varId=${id} visits=${count} type=${t?.toString().slice(0,80)} fromEdges=[${edgeTypes}] name=${meta.text.get(id) || '?'}`);
                }
                break;
            }
            const nodeId = this.worklist.shift()!;
            const cnt = (visitCount.get(nodeId) || 0) + 1;
            visitCount.set(nodeId, cnt);
            this.graph.traceEvent("propagate:before", nodeId);
            let worklist;
            worklist = this.strategy.propagate(nodeId, this.graph);
            this.worklist.push(...worklist);
            this.graph.traceAffected("propagate:affected", nodeId, worklist);
            this.graph.traceEvent("propagate:after", nodeId);
            worklist = this.graph.extend(nodeId);
            this.worklist.push(...worklist);
            this.graph.traceAffected("extend:affected", nodeId, worklist);
            this.graph.traceEvent("extend:after", nodeId);
        }
        if (iteration > maxIterations) {
            console.error("Solver terminated due to possible infinite loop");
        }
    }

    output(eva = true): any {
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

        // 类型分布统计
        const stats = this.graph.typeStats();
        const statsOut = path.join(outputDir, "typestats.json");
        writeJsonStream(statsOut, stats);

        // 评估标注
        if (eva) {
            const evalResult = this.graph.evaluate();
            const evalOut = path.join(outputDir, "evaluation.json");
            writeJsonStream(evalOut, evalResult);
        }

        console.log(`Done. Output written to ${outputDir}`);
    }
}
