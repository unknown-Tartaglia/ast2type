import { meta, outputDir, solver, tNode } from "../ast2type";
import { VarId, TypeId } from "./fact"
import { NodeState, tNodeStore, DeterminantNodeState } from "./nType";
import * as path from "path";
import * as fs from "fs";

export class TypeGraph {
    nodes = new Map<VarId, NodeState>()
    state2node = new Map<NodeState, Set<VarId>>()
    toEdges = new Map<VarId, Set<Edge>>()
    fromEdges = new Map<VarId, Set<Edge>>()
    delayEdges = new Map<VarId, { from: VarId, argIdx: number, edgeType: string }[]>()
    // trace
    traceTarget: number | null = null
    private traceLog: any[] = []
    private traceStep = 0


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

        // trace: 新边指向追踪目标
        if (to === this.traceTarget) {
            this.traceStep++;
            const ownType = this.nodes.get(to);
            const fromType = this.nodes.get(from);
            this.traceLog.push({
                step: this.traceStep,
                action: "addEdge",
                from,
                edgeType: type,
                fromType: fromType?.toString() ?? "unknown",
                ownType: ownType?.toString() ?? "unknown",
            });
        }
    }

    addDelayedEdge(from: VarId, toFuncVarId: VarId, argIdx: number, edgeType: string) {
        if (!this.delayEdges.has(toFuncVarId)) {
            this.delayEdges.set(toFuncVarId, []);
        }
        this.delayEdges.get(toFuncVarId)!.push({ from, argIdx, edgeType });
    }

    mergeNodes(source: VarId, target: VarId) {
        if (source === target) return;

        // 合并 meta 信息：将 source 的 meta 信息复制到 target（如果 target 没有）
        if (meta.objectName.has(source) && !meta.objectName.has(target)) meta.objectName.set(target, meta.objectName.get(source)!);
        if (meta.className.has(source) && !meta.className.has(target)) meta.className.set(target, meta.className.get(source)!);
        if (meta.interfaceName.has(source) && !meta.interfaceName.has(target)) meta.interfaceName.set(target, meta.interfaceName.get(source)!);
        if (meta.propName.has(source) && !meta.propName.has(target)) meta.propName.set(target, meta.propName.get(source)!);
        if (meta.enumName.has(source) && !meta.enumName.has(target)) meta.enumName.set(target, meta.enumName.get(source)!);
        if (meta.enumMemberName.has(source) && !meta.enumMemberName.has(target)) meta.enumMemberName.set(target, meta.enumMemberName.get(source)!);
        if (meta.funcName.has(source) && !meta.funcName.has(target)) meta.funcName.set(target, meta.funcName.get(source)!);
        if (meta.paramName.has(source) && !meta.paramName.has(target)) meta.paramName.set(target, meta.paramName.get(source)!);
        if (meta.paramIndex.has(source) && !meta.paramIndex.has(target)) meta.paramIndex.set(target, meta.paramIndex.get(source)!);
        // funcParamMap 和 funcBindMap 需要特殊处理，暂时跳过

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

        // trace
        if (node === this.traceTarget) {
            this.traceStep++;
            this.traceLog.push({
                step: this.traceStep,
                action: "setType",
                ownType: val.toString(),
                sources: this._traceSources(node),
            });
        }

        if (!this.delayEdges.has(node)) return;
        const funcNode = val.getFuncVaridorNull();
        if (funcNode === null) return;

        const delayed = this.delayEdges.get(node)!;
        for (const { from, argIdx, edgeType } of delayed) {
            if (meta.funcParamMap.has(funcNode)) {
                const paramMap = meta.funcParamMap.get(funcNode)!;
                const paramVarId = paramMap.get(argIdx);
                if (paramVarId === undefined) {
                    console.error(`ArgRule: paramVarId not found for funcVarId ${funcNode}, argIdx ${argIdx}`)
                    continue;
                }
                this.addEdge(from, paramVarId, edgeType);
                solver.worklist.push(from);
                // console.log(`Added delayed edge from ${from} to ${paramVarId} for argument index ${argIdx} with edge type ${edgeType}`);
            } else {
                console.error(`ArgRule: funcVarId ${funcNode} does not have paramMap, cannot add delayed edge from ${from} for argument index ${argIdx} with edge type ${edgeType}`);
            }
        }
        this.delayEdges.delete(node);
    }

    setRetType(node: VarId, typeId: number) {
        const oldState = this.nodes.get(node);
        oldState?.addReturnType(new DeterminantNodeState(typeId));
    }

    private _traceSources(node: VarId) {
        const sources: any[] = [];
        for (const edge of this.getFromEdges(node)) {
            const fromType = this.nodes.get(edge.from);
            sources.push({
                from: edge.from,
                edgeType: edge.type,
                fromType: fromType?.toString() ?? "unknown",
                cand: edge.cand?.toString() ?? null,
            });
        }
        return sources;
    }

    /** 记录 trace 事件（propagate/extend 等不经过 setType 的步骤） */
    traceEvent(action: string, node: VarId) {
        if (node !== this.traceTarget) return;
        const ownType = this.nodes.get(node);
        this.traceStep++;
        this.traceLog.push({
            step: this.traceStep,
            action,
            ownType: ownType?.toString() ?? "unknown",
            sources: this._traceSources(node),
        });
    }

    /** 记录 propagate/extend 影响了哪些节点的类型变化 */
    traceAffected(action: string, targetNode: VarId, affected: VarId[]) {
        if (targetNode !== this.traceTarget || affected.length === 0) return;
        const details = affected.map(id => {
            const t = this.nodes.get(id);
            return { id, type: t?.toString() ?? "unknown" };
        });
        this.traceStep++;
        this.traceLog.push({
            step: this.traceStep,
            action,
            targetNode,
            affected: details,
        });
    }

    /** 输出 trace 日志到文件 */
    dumpTrace(dir: string) {
        if (!this.traceTarget || this.traceLog.length === 0) return;
        const out = path.join(dir, "trace.json");
        fs.writeFileSync(out, JSON.stringify(this.traceLog, null, 2), "utf-8");
        console.log(`[trace] ${this.traceLog.length} events for varId ${this.traceTarget} → ${out}`);
    }

    getToEdges(node: VarId): Set<Edge> {
        return this.toEdges.get(node) || new Set<Edge>();
    }

    getFromEdges(node: VarId): Set<Edge> {
        return this.fromEdges.get(node) || new Set<Edge>();
    }

    setSrcType(edge: Edge, val: NodeState) {
        edge.cand = val;
        if (edge.to === this.traceTarget) {
            this.traceStep++;
            const ownType = this.nodes.get(edge.to);
            this.traceLog.push({
                step: this.traceStep,
                action: "setSrcType",
                from: edge.from,
                edgeType: edge.type,
                candType: val.toString(),
                ownType: ownType?.toString() ?? "unknown",
                sources: this._traceSources(edge.to),
            });
        }
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
                const changed = fromType.addProperty(meta.propName.get(nodeId)!, ty);
                if (changed) {
                    this.setType(edge.from, fromType);
                    worklist.push(edge.from);
                }
            }
            if (edge.type === "ArrayElement") {
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                const changed = fromType.addElement(ty);
                if (changed) {
                    this.setType(edge.from, fromType);
                    worklist.push(edge.from);
                }
            }
            // 处理参数边：从函数指向参数，当前节点是参数
            if (edge.type === "param") {
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                const changed = fromType.addParam(nodeId, ty);
                if (changed) {
                    this.setType(edge.from, fromType);
                    worklist.push(edge.from);
                }
            }
            // 处理返回边：从函数指向返回值，当前节点是返回值
            if (edge.type === "return") {
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                const changed = fromType.addReturnType(ty);
                if (changed) {
                    this.setType(edge.from, fromType);
                    worklist.push(edge.from);
                }
            }
            // 处理枚举成员边：从enum指向member，当前节点是member
            if (edge.type === "enumMember") {
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                // 将member的类型设置为枚举类型
                if (!ty.equals(fromType)) {
                    this.setType(nodeId, fromType);
                    worklist.push(nodeId);
                }
            }
            // 注解边和起源边不做类型传播，只保留边关系
            if (edge.type === "annotation" || edge.type === "returnAnnotation" || edge.type === "origin") {
                // 不做类型传播，只保留边
                continue;
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
            if (edge.type === "call") {
                // 函数调用：将函数返回类型传播给调用结果
                const toType = this.nodes.get(edge.to);
                const newType = ty.getReturnType();
                if (!newType) continue;
                if (!toType || !toType.equals(newType)) {
                    this.setType(edge.to, newType);
                    worklist.push(edge.to);
                }
            }
            // 注解边、返回注解边、起源边和枚举成员边在getToEdges方向不需要特殊处理
            if (edge.type === "annotation" || edge.type === "returnAnnotation" || edge.type === "origin" || edge.type === "enumMember") {
                // 不做类型传播，只保留边
                continue;
            }
        }
        return worklist;
    }

    toJson() {
        const nodes: any[] = [];
        const edges: any[] = [];
        const unknownNodes: Set<VarId> = new Set<VarId>();
        for (const [nodeId, state] of this.nodes) {
            let file = meta.file.get(nodeId);
            file = file ? path.join(file.split("ast" + require("path").sep)[0].replace("_output", ""), file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "")) : "unknown_file";
            nodes.push({
                id: nodeId,
                label: meta.text.get(nodeId) || `var_${nodeId}`,
                type: state.toString(),
                text: meta.text.get(nodeId) || "",
                file: file,
                position: meta.pos.get(nodeId) || null,
                fullType: JSON.stringify(state.toJson(), null, 2) || null,
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
            let file = meta.file.get(unk);
            file = file ? path.join(file.split("ast" + require("path").sep)[0].replace("_output", ""), file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "")) : "unknown_file";
            nodes.push({
                id: unk,
                label: meta.text.get(unk) || `var_${unk}`,
                type: "unknown",
                text: meta.text.get(unk) || "",
                file: file,
                position: meta.pos.get(unk) || null,
                fullType: null,
            });
        }
        return { nodes, edges };
    }

    toAnno() {
        const outJson = [];
        const unkJson = [];
        for (const [nodeId, state] of this.nodes) {
            const id = nodeId;
            const ty = tNode.get(state.val);
            let file = meta.file.get(id);
            let relapath = file ? file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "") : "unknown_relapath";
            file = file ? path.join(file.split("ast" + require("path").sep)[0].replace("_output", ""), file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "")) : "unknown_file";
            if (!meta.v8Kind.has(id)) continue;
            if (state.toAnno() === "unknown") continue;
            outJson.push({
                context: meta.context.get(id) || "",
                exprText: meta.text.get(id) || "",
                exprKind: meta.v8Kind.get(id) || "",
                morphKind: meta.kind.get(id) || "",
                location: meta.offset.get(id) || -1,
                pos: meta.pos.get(id) || null,
                type: state.toAnno(),
                constant: ty?.kind === "literal" ? ty.value : undefined,
                relapath: relapath,
                file: file,
            })
        }
        for (const edge of this.toEdges.values()) {
            for (const e of edge) {
                let id = e.from;
                // 筛选无入边且无类型信息的节点（即完全孤立的节点，可能是某些特殊表达式或标识符），加入未知列表
                if (this.getFromEdges(id).size === 0 && !this.nodes.has(id)) {
                    let file = meta.file.get(id);
                    let relapath = file ? file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "") : "unknown_relapath";
                    file = file ? path.join(file.split("ast" + require("path").sep)[0].replace("_output", ""), file.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "")) : "unknown_file";
                    unkJson.push({
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
        }
        return [outJson, unkJson];
    }

    /** 递归判断两个 TypeId 是否兼容 */
    private _typesCompatible(inferredId: TypeId, expectedId: TypeId): boolean {
        // 严格相等
        if (inferredId === expectedId) return true;
        // any / unknown 与任何类型兼容
        if (inferredId === tNode.ANY || expectedId === tNode.ANY) return true;
        if (inferredId === tNode.UNKNOWN || expectedId === tNode.UNKNOWN) return true;

        const inf = tNode.get(inferredId);
        const exp = tNode.get(expectedId);
        if (!inf || !exp) return false;

        // 字面量 → 原始类型
        if (inf.kind === "literal" && exp.kind === "primitive") {
            return (typeof inf.value === "number" && exp.name === "number") ||
                   (typeof inf.value === "string" && exp.name === "string") ||
                   (typeof inf.value === "boolean" && exp.name === "boolean");
        }

        // 推导类型是 union → 任一成员与期望兼容即可（推导偏宽算正确）
        if (inf.kind === "union") {
            return inf.types.some(t => this._typesCompatible(t, expectedId));
        }

        // 期望类型是 union → 推导与任一成员兼容即可
        if (exp.kind === "union") {
            return exp.types.some(t => this._typesCompatible(inferredId, t));
        }

        // 数组兼容
        if (inf.kind === "array" && exp.kind === "array") {
            return this._typesCompatible(inf.elementType, exp.elementType);
        }

        // 推导是数组，期望是命名对象 Array → 兼容
        if (inf.kind === "array" && exp.kind === "object" && exp.name === "Array") {
            return true;
        }

        // 函数兼容：比较返回类型
        if (inf.kind === "function" && exp.kind === "function") {
            return this._typesCompatible(inf.returnType, exp.returnType);
        }

        // 同名 object
        if (inf.kind === "object" && exp.kind === "object") {
            if (inf.name && exp.name && inf.name === exp.name) return true;
        }

        return false;
    }

    evaluate() {
        // 评估标注的准确性，基于annotation节点和returnAnnotation节点
        console.log("========== Evaluating type annotation consistency ==========");

        const result = {
            total: 0,
            correct: 0,
            wrong: 0,
            missing: 0,
            any: 0, // 统计any出现次数
            unknown: 0, // 统计无法判断类型的注释出现次数
            rightEdges: [] as { kind: string, from: VarId, to: VarId, inferredType: string, expectedType: string }[],
            wrongEdges: [] as { kind: string, from: VarId, to: VarId, inferredType: string, expectedType: string }[],
            undeterminedEdges: [] as { kind: string, from: VarId, to: VarId, inferredType: string, expectedType: string }[],
        };

        // // 从output/inferinfo.json加载外部推导类型信息
        // const inferredTypes: Map<VarId, string> = new Map<VarId, string>();
        // try {
        //     const inferInfoPath = path.join(outputDir, "inferinfo.json");
        //     if (fs.existsSync(inferInfoPath)) {
        //         const inferData = JSON.parse(fs.readFileSync(inferInfoPath, "utf-8"));
        //         for (const item of inferData) {
        //             if (item.id === undefined || item.type === undefined) {
        //                 console.warn(`Invalid infer info item: ${JSON.stringify(item)}, skipping`);
        //                 continue;
        //             }
        //             inferredTypes.set(item.id, item.type);
        //         }
        //         console.log(`Loaded inferred types for ${inferredTypes.size} nodes from ${inferInfoPath}`);
        //     } else {
        //         console.warn(`Inferred types file not found at ${inferInfoPath}, skipping loading inferred types`);
        //     }
        // } catch (err) {
        //     console.error(`Error loading inferred types: ${err}`);
        // }

        // 遍历所有边
        for (const [_, edgeSet] of this.toEdges) {
            for (const edge of edgeSet) {
                if (edge.type !== "annotation" && edge.type !== "returnAnnotation") {
                    continue;
                }

                result.total++;

                const fromState = this.nodes.get(edge.from);
                const toState = this.nodes.get(edge.to);

                // === 处理标注类型（期望类型）===
                if (!toState) {
                    // 标注类型节点没有类型状态，视为未知标注
                    result.unknown++;
                    continue;
                }

                const expectedTypeStr = toState.toString();
                const expectedTypeId = toState.val;

                // 跳过any类型比较
                if (expectedTypeId === tNode.ANY) {
                    result.any++;
                    continue;
                }
                // 跳过unknown类型比较
                if (expectedTypeId === tNode.UNKNOWN) {
                    result.unknown++;
                    continue;
                }

                // === 处理推导类型 ===
                let inferredState = fromState || null;
                if (edge.type === "returnAnnotation") inferredState = fromState ? fromState.getReturnType() : null;

                if (!inferredState) {
                    // 没有推导类型信息，视为缺失
                    result.missing++;
                    result.undeterminedEdges.push({
                        kind: edge.type,
                        from: edge.from,
                        to: edge.to,
                        inferredType: "missing",
                        expectedType: expectedTypeStr
                    });
                    continue;
                }

                const inferredTypeStr = inferredState.toString();
                const inferredTypeId = inferredState.val;

                // 检查推导类型是否为unknown
                if (inferredTypeId === tNode.UNKNOWN) {
                    result.missing++;
                    result.undeterminedEdges.push({
                        kind: edge.type,
                        from: edge.from,
                        to: edge.to,
                        inferredType: inferredTypeStr,
                        expectedType: expectedTypeStr
                    });
                    continue;
                }

                // === 类型兼容性检查 ===
                const isCompatible = this._typesCompatible(inferredTypeId, expectedTypeId);

                if (isCompatible) {
                    result.correct++;
                    result.rightEdges.push({
                        kind: edge.type,
                        from: edge.from,
                        to: edge.to,
                        inferredType: inferredTypeStr,
                        expectedType: expectedTypeStr
                    });
                } else {
                    result.wrong++;
                    result.wrongEdges.push({
                        kind: edge.type,
                        from: edge.from,
                        to: edge.to,
                        inferredType: inferredTypeStr,
                        expectedType: expectedTypeStr
                    });
                }
            }
        }

        // 输出汇总报告
        const other = result.any + result.unknown;
        const acc = result.correct > 0 ? result.correct / (result.correct + result.wrong) : 0;
        const cov = result.correct + result.wrong > 0 ? (result.correct + result.wrong) / (result.correct + result.wrong + result.missing) : 0;

        // 输出正确的边列表
        if (result.rightEdges.length > 0) {
            console.log("\n--- Correct annotations ---");
            for (const w of result.rightEdges) {
                const fromText = meta.text.get(w.from) || `var_${w.from}`;
                const toText = meta.text.get(w.to) || `var_${w.to}`;
                console.log(
                    `  [${w.kind}] ${fromText}[${w.from}] (${w.inferredType})  ===  ${toText} (${w.expectedType})`
                );
            }
        }

        // 输出详细错误列表
        if (result.wrongEdges.length > 0) {
            console.log("\n--- Type mismatches ---");
            for (const w of result.wrongEdges) {
                const fromText = meta.text.get(w.from) || `var_${w.from}`;
                const toText = meta.text.get(w.to) || `var_${w.to}`;
                console.log(
                    `  [${w.kind}] ${fromText}[${w.from}] (${w.inferredType})  !==  ${toText} (${w.expectedType})`
                );
            }
        }

        console.log("========== Evaluation Report ==========");
        console.log(`Total annotations: ${result.total}`);
        console.log(`Correct: ${result.correct}`);
        console.log(`Wrong: ${result.wrong}`);
        console.log(`Missing: ${result.missing}`);
        console.log(`Ignored: any * ${result.any} + unknown * ${result.unknown} = ${other}`);
        console.log(`Coverage: ${(cov * 100).toFixed(2)}%`);
        console.log(`Effective accuracy: ${(acc * 100).toFixed(2)}%`);

        return result;
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

