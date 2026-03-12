import { ConditionalExpression, ConstructorTypeNode } from "ts-morph";
import { meta, solver, tNode } from "../ast2type";
import { VarId } from "./fact"
import { NodeState, tNodeStore, DeterminantNodeState } from "./nType";
import * as path from "path";

export class TypeGraph {
    nodes = new Map<VarId, NodeState>()
    state2node = new Map<NodeState, Set<VarId>>()
    toEdges = new Map<VarId, Set<Edge>>()
    fromEdges = new Map<VarId, Set<Edge>>()
    delayEdges = new Map<VarId, { from: VarId, argIdx: number, edgeType: string }[]>()


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
                console.log(`Added delayed edge from ${from} to ${paramVarId} for argument index ${argIdx} with edge type ${edgeType}`);
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
            // 处理参数边：从函数指向参数，当前节点是参数
            if (edge.type === "param") {
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                const changed = fromType.addParam(nodeId, ty);
                if (changed) worklist.push(edge.from);
            }
            // 处理返回边：从函数指向返回值，当前节点是返回值
            if (edge.type === "return") {
                const fromType = this.nodes.get(edge.from);
                if (!fromType) continue;
                const changed = fromType.addReturnType(ty);
                if (changed) worklist.push(edge.from);
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
            nodes.push({
                id: nodeId,
                label: meta.text.get(nodeId) || `var_${nodeId}`,
                type: state.toString(),
                text: meta.text.get(nodeId) || "",
                file: meta.file.get(nodeId) || null,
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
            nodes.push({
                id: unk,
                label: meta.text.get(unk) || `var_${unk}`,
                type: "unknown",
                text: meta.text.get(unk) || "",
                file: meta.file.get(unk) || null,
                position: meta.pos.get(unk) || null,
                fullType: null,
            });
        }
        return { nodes, edges };
    }

    toAnno() {
        const outJson = [];
        for (const [nodeId, state] of this.nodes) {
            const id = nodeId;
            const ty = tNode.get(state.val);
            if (!meta.v8Kind.has(id)) continue;
            outJson.push({
                context: meta.context.get(id) || "",
                exprText: meta.text.get(id) || "",
                exprKind: meta.v8Kind.get(id) || "",
                morphKind: meta.kind.get(id) || "",
                location: meta.offset.get(id) || -1,
                pos: meta.pos.get(id) || null,
                type: state.toAnno(),
                constant: ty?.kind === "literal" ? ty.value : undefined,
                relapath: meta.file.get(id)!.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, ""),
                file: path.join(meta.file.get(id)!.split("ast" + require("path").sep)[0].replace("_output", ""), meta.file.get(id)!.split("ast" + require("path").sep)[1].replace(/\^/g, require("path").sep).replace(/\.ast\.json$/, "")),
            })
        }
        return outJson;
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
        };

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
                    result.missing++;
                    result.wrongEdges.push({
                        kind: edge.type,
                        from: edge.from,
                        to: edge.to,
                        inferredType: "unknown",
                        expectedType: expectedTypeStr
                    });
                    continue;
                }

                const inferredTypeStr = inferredState.toString();
                const inferredTypeId = inferredState.val;

                // 检查推导类型是否为unknown
                if (inferredTypeId === tNode.UNKNOWN) {
                    result.missing++;
                    result.wrongEdges.push({
                        kind: edge.type,
                        from: edge.from,
                        to: edge.to,
                        inferredType: inferredTypeStr,
                        expectedType: expectedTypeStr
                    });
                    continue;
                }

                // === 类型兼容性检查 ===
                let isCompatible = false;

                // 1. 严格相等
                if (inferredState.equals(toState)) {
                    isCompatible = true;
                }
                // 2. any可以赋值给任何类型
                else if (inferredTypeId === tNode.ANY) {
                    isCompatible = true;
                }
                // 3. 字面量到原始类型的赋值
                else {
                    const inferredType = tNode.get(inferredTypeId);
                    const expectedType = tNode.get(expectedTypeId);

                    if (inferredType && expectedType) {
                        // 字面量到原始类型
                        if (inferredType.kind === "literal" && expectedType.kind === "primitive") {
                            const litValue = inferredType.value;
                            const primName = expectedType.name;
                            if (typeof litValue === "number" && primName === "number") {
                                isCompatible = true;
                            } else if (typeof litValue === "string" && primName === "string") {
                                isCompatible = true;
                            } else if (typeof litValue === "boolean" && primName === "boolean") {
                                isCompatible = true;
                            }
                        }
                        // 数组元素类型兼容
                        else if (inferredType.kind === "array" && expectedType.kind === "array") {
                            const infElem = new DeterminantNodeState(inferredType.elementType);
                            const expElem = new DeterminantNodeState(expectedType.elementType);
                            if (infElem.equals(expElem)) {
                                isCompatible = true;
                            }
                        }
                    }
                }

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

        console.log("========== Evaluation Report ==========");
        console.log(`Total annotations: ${result.total}`);
        console.log(`Correct: ${result.correct}`);
        console.log(`Wrong: ${result.wrong}`);
        console.log(`Missing: ${result.missing}`);
        console.log(`Ignored: any * ${result.any} + unknown * ${result.unknown} = ${other}`);
        console.log(`Coverage: ${(cov * 100).toFixed(2)}%`);
        console.log(`Effective accuracy: ${(acc * 100).toFixed(2)}%`);

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
                // 跳过推导类型为unknown的（这些已经在missing中）
                if (w.inferredType === "unknown") continue;
                const fromText = meta.text.get(w.from) || `var_${w.from}`;
                const toText = meta.text.get(w.to) || `var_${w.to}`;
                console.log(
                    `  [${w.kind}] ${fromText}[${w.from}] (${w.inferredType})  !==  ${toText} (${w.expectedType})`
                );
            }

            console.log("\n--- Type underived ---");
            for (const w of result.wrongEdges) {
                // 只显示推导类型为unknown的
                if (w.inferredType !== "unknown") continue;
                const fromText = meta.text.get(w.from) || `var_${w.from}`;
                const toText = meta.text.get(w.to) || `var_${w.to}`;
                console.log(
                    `  [${w.kind}] ${fromText}[${w.from}] (${w.inferredType})  !==  ${toText} (${w.expectedType})`
                );
            }
        }

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

