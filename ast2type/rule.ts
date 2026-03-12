import { meta, tNode } from "../ast2type";
import { AllocArrayFact, AllocLiteralFact, AllocObjFact, ArrayElementFact, AnnotFact, BinaryOpFact, CallFact, Fact, FlowFact, NewInstanceFact, ParamFact, ArgFact, ReturnStmtFact, ReturnVoidFact, ReturnAnnotFact, AllocFunctionFact, PropFact, SameIDFact, TypeId, UnaryOpFact, VarId, TernaryOpFact, AllocEnumFact, EnumMemberFact, AllocInterfaceFact, AllocClassFact, AllocPrimitiveFact, OriginFact, AliasFact } from "./fact"

// 规则工厂
export class RuleStore {
    private rules: Rule[] = [];
    
    constructor() {
      this.registerRules();
    }
    
    private registerRules(): void {
      this.rules.push(
        new FlowRule(),
        new UnaryOpRule(),
        new BinaryOpRule(),
        new TernaryOpRule(),
        new AllocObjRule(),
        new PropRule(),
        new AllocLiteralRule(),
        new AllocArrayRule(),
        new ArrayElementRule(),
        new NewInstanceRule(),
        new SameIDRule(),
        new CallRule(),
        new ParamRule(),
        new ArgRule(),
        new ReturnStmtRule(),
        new ReturnVoidRule(),
        new ReturnAnnotRule(),
        new AllocFunctionRule(),
        new AnnotRule(),
        new AllocEnumRule(),
        new EnumMemberRule(),
        new AllocInterfaceRule(),
        new AllocClassRule(),
        new AllocPrimitiveRule(),
        new OriginRule(),
        new AliasRule()
      );
    }
    
    applyRule(fact: Fact): GraphEffect[] {
      const rule = this.rules.find(r => r.canHandle(fact));
      if (!rule) {
        console.warn(`No rule found for fact kind: ${(fact as any).kind}`);
        return [];
      }
      return rule.apply(fact as any);
    }
    
    // 批量处理
    applyRules(facts: Fact[]): GraphEffect[] {
      return facts.flatMap(fact => this.applyRule(fact));
    }
}

export interface Rule {
    apply(fact: Fact): GraphEffect[]
    canHandle(fact: Fact): boolean
}

type GraphEffect =
    | { kind: 'mergeNode'; source: VarId; target: VarId }
    | { kind: 'genType'; node: VarId; type: TypeId }
    | { kind: 'addEdge'; from: VarId; to: VarId; edgeType: string }
    | { kind: 'delayEdge'; from: VarId; toFuncVarId: VarId; argIdx: number; edgeType: string }
    | { kind: 'setVoid'; node: VarId }

class FlowRule implements Rule {
    apply(fact: FlowFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.from, to: fact.to, edgeType: "sameType"}]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Flow"
    }
}

class UnaryOpRule implements Rule {
    apply(fact: UnaryOpFact): GraphEffect[] {
        switch (fact.operator) {
            // 一元加号：转换为数字
            case "+":
            // 一元减号：转换为数字
            case "-":
            // 按位非：转换为数字
            case "~":
                return [{ kind: "genType", node: fact.result, type: tNode.NUMBER }];
            // typeof 操作符：返回字符串
            case "typeof":
                return [{ kind: "genType", node: fact.result, type: tNode.STRING }];
            // 逻辑非：返回布尔值
            case "!":
                return [{ kind: "genType", node: fact.result, type: tNode.BOOLEAN }];
            // void 操作符：返回 undefined
            case "void":
                return [{ kind: "genType", node: fact.result, type: tNode.newTypeNode({ kind: "primitive", name: "undefined" })}];
            // delete 操作符：返回布尔值
            case "delete":
                return [{ kind: "genType", node: fact.result, type: tNode.BOOLEAN }];
            default:
                console.warn(`UnaryOpRule: unhandled operator "${fact.operator}"`);
                return [];
        }
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "UnaryOp"
    }
}

class BinaryOpRule implements Rule {
    apply(fact: BinaryOpFact): GraphEffect[] {
        switch (fact.operator) {
            // 在这里可以根据不同的二元操作符添加不同的处理逻辑
            case "=":
            case "+=":
            case "-=":
            case "*=":
            case "/=":
            case "%=":
            case "**=":
            case "&=":
            case "|=":
            case "^=":
            case "<<=":
            case ">>=":
            case ">>>=":
            case "&&=":
            case "||=":
            case "??=":
                return [{ kind: "addEdge", from: fact.left, to: fact.result, edgeType: "sameType" },
                        { kind: "addEdge", from: fact.right, to: fact.left, edgeType: "sameType" }];
            case "+":
                return [{ kind: "addEdge", from: fact.left, to: fact.result, edgeType: "sameType" },
                    { kind: "addEdge", from: fact.right, to: fact.result, edgeType: "sameType" }];
            case "-":
            case "*":
            case "/":
            case "%":
            case "**":
                return [{ kind: "genType", node: fact.result, type: tNode.NUMBER },
                        { kind: "addEdge", from: fact.result, to: fact.left, edgeType: "sameType" },
                        { kind: "addEdge", from: fact.result, to: fact.right, edgeType: "sameType" }];
            case "&&":
            case "||":
            case "??":
                return [{ kind: "addEdge", from: fact.left, to: fact.result, edgeType: "sameType" },
                        { kind: "addEdge", from: fact.right, to: fact.result, edgeType: "sameType" }];
            case "<":
            case "<=":
            case ">":
            case ">=":
            case "==":
            case "===":
            case "!=":
            case "!==":
                // 这些操作符通常返回布尔值，可以根据需要生成布尔类型
                return [{ kind: "genType", node: fact.result, type: tNode.newTypeNode({ kind: "primitive", name: "boolean" })}];
            case "&":
            case "|":
            case "^":
            case "<<":
            case ">>":
            case ">>>":
                return [{ kind: "addEdge", from: fact.left, to: fact.result, edgeType: "sameType" },
                        { kind: "addEdge", from: fact.right, to: fact.result, edgeType: "sameType" }];
            case "instanceof":
            case "in":
                // instanceof 和 in 操作符返回布尔值
                return [{ kind: "genType", node: fact.result, type: tNode.BOOLEAN }];
            default:
                return [];
        }
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "BinaryOp"
    }
}

class AllocObjRule implements Rule {
    apply(fact: AllocObjFact): GraphEffect[] {
        return [{ kind: "genType", node: fact.varId, type: tNode.newTypeNode({ kind: "object", name: meta.objectName.get(fact.varId) ?? `obj_${fact.varId}`, id: fact.varId, properties: {} })}]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocObj"
    }
}

class PropRule implements Rule {
    apply(fact: PropFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.objVarId, to: fact.propVarId, edgeType: "property" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Prop"
    }
}

class AllocLiteralRule implements Rule {
    apply(fact: AllocLiteralFact): GraphEffect[] {
        return [{ kind: "genType", node: fact.varId, type: tNode.newTypeNode({ kind: "literal", value: fact.value})}]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocLiteral"
    }
}

class AllocArrayRule implements Rule {
    apply(fact: AllocArrayFact): GraphEffect[] {
        return [{ kind: "genType", node: fact.varId, type: tNode.newTypeNode({ kind: "array", elementType: tNode.UNKNOWN})}]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocArray"
    }
}

class ArrayElementRule implements Rule {
    apply(fact: ArrayElementFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.arrayVarId, to: fact.elementVarId, edgeType: "ArrayElement" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "ArrayElement"
    }
}

class NewInstanceRule implements Rule {
    apply(fact: NewInstanceFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.classVarId, to: fact.instanceVarId, edgeType: "sameType" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "NewInstance"  
    }
}

class SameIDRule implements Rule {
    apply(fact: SameIDFact): GraphEffect[] {
        return [{ kind: "mergeNode", source: fact.source, target: fact.target }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "SameID"
    }
}

class CallRule implements Rule {
    apply(fact: CallFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.func, to: fact.result, edgeType: "call" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Call"
    }
}

class ParamRule implements Rule {
    apply(fact: ParamFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.funcVarId, to: fact.paramVarId, edgeType: "param" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Param"
    }
}

class ArgRule implements Rule {
    apply(fact: ArgFact): GraphEffect[] {
        // 查找真正的函数变量ID（可能通过标识符绑定）
        let funcVarId = fact.funcVarId
        if (meta.funcBindMap.has(funcVarId)) {
            funcVarId = meta.funcBindMap.get(funcVarId)!
        } else {
        }
        // 查找对应索引的形参变量ID
        const paramMap = meta.funcParamMap.get(funcVarId)
        if (!paramMap) {
            console.warn(`ArgRule: funcParamMap not found for funcVarId ${funcVarId}`)
            return [ { kind: "delayEdge", from: fact.argVarId, toFuncVarId: funcVarId, argIdx: fact.argIdx, edgeType: "ArgToParam" } ]
        }
        const paramVarId = paramMap.get(fact.argIdx)
        if (paramVarId === undefined) {
            console.warn(`ArgRule: paramVarId not found for funcVarId ${funcVarId}, argIdx ${fact.argIdx}`)
            return []
        }
        // 创建从实参到形参的边
        return [{ kind: "addEdge", from: fact.argVarId, to: paramVarId, edgeType: "ArgToParam" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Arg"
    }
}

class ReturnStmtRule implements Rule {
    apply(fact: ReturnStmtFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.funcVarId, to: fact.returnVarId, edgeType: "return" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "ReturnStmt"
    }
}

class ReturnVoidRule implements Rule {
    apply(_fact: ReturnVoidFact): GraphEffect[] {
        // returnVoid fact 可能不需要产生效果，函数返回类型可能通过其他方式推断
        return [{ kind: "setVoid", node: _fact.funcVarId }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "ReturnVoid"
    }
}

class ReturnAnnotRule implements Rule {
    apply(fact: ReturnAnnotFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.funcVarId, to: fact.typeVarId, edgeType: "returnAnnotation" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "ReturnAnnot"
    }
}

class AllocFunctionRule implements Rule {
    apply(fact: AllocFunctionFact): GraphEffect[] {
        // 创建初始函数类型，参数为空，返回类型为UNKNOWN
        const funcType = tNode.newTypeNode({
            kind: "function",
            name: meta.funcName.get(fact.varId) ?? `func_${fact.varId}`,
            id: fact.varId,
            param: {} as Record<number, {id: number; type: number}>,
            returnType: tNode.UNKNOWN
        });
        const effects: GraphEffect[] = [{ kind: "genType", node: fact.varId, type: funcType }]
        // 函数绑定到标识符，添加sameType边
        if (fact.bind !== undefined && fact.bind !== fact.varId) {
            effects.push({ kind: "addEdge", from: fact.varId, to: fact.bind, edgeType: "sameType" })
        }
        return effects
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocFunction"
    }
}

class AnnotRule implements Rule {
    apply(fact: AnnotFact): GraphEffect[] {
        // 类型注解：target 变量具有 type 类型
        return [{ kind: "addEdge", from: fact.target, to: fact.type, edgeType: "annotation" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Annot"
    }
}

class TernaryOpRule implements Rule {
    apply(fact: TernaryOpFact): GraphEffect[] {
        // 三元操作符 condition ? trueExpr : falseExpr
        // 结果类型是 trueExpr 和 falseExpr 类型的并集
        return [
            { kind: "addEdge", from: fact.true, to: fact.result, edgeType: "sameType" },
            { kind: "addEdge", from: fact.false, to: fact.result, edgeType: "sameType" }
        ]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "TernaryOp"
    }
}

class AllocEnumRule implements Rule {
    apply(fact: AllocEnumFact): GraphEffect[] {
        // 创建枚举类型
        const enumType = tNode.newTypeNode({
            kind: "enum",
            name: meta.enumName.get(fact.varId) ?? `enum_${fact.varId}`,
            members: {}
        });
        return [{ kind: "genType", node: fact.varId, type: enumType }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocEnum"
    }
}

class EnumMemberRule implements Rule {
    apply(fact: EnumMemberFact): GraphEffect[] {
        // 枚举成员：将成员变量与枚举类型关联
        return [{ kind: "addEdge", from: fact.enumVarId, to: fact.memberVarId, edgeType: "enumMember" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "EnumMember"
    }
}

class AllocInterfaceRule implements Rule {
    apply(fact: AllocInterfaceFact): GraphEffect[] {
        // 创建接口类型（类似于对象类型）
        const interfaceType = tNode.newTypeNode({
            kind: "object",
            name: meta.interfaceName.get(fact.varId) ?? `interface_${fact.varId}`,
            id: fact.varId,
            properties: {}
        });
        return [{ kind: "genType", node: fact.varId, type: interfaceType }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocInterface"
    }
}

class AllocClassRule implements Rule {
    apply(fact: AllocClassFact): GraphEffect[] {
        // 创建类类型（类似于对象类型，可能有构造函数）
        const classType = tNode.newTypeNode({
            kind: "object",
            name: meta.className.get(fact.varId) ?? `class_${fact.varId}`,
            id: fact.varId,
            properties: {}
        });
        return [{ kind: "genType", node: fact.varId, type: classType }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocClass"
    }
}

class AllocPrimitiveRule implements Rule {
    apply(fact: AllocPrimitiveFact): GraphEffect[] {
        // 原始类型分配：直接使用给定的typeId
        return [{ kind: "genType", node: fact.varId, type: fact.typeId }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "AllocPrimitive"
    }
}

class OriginRule implements Rule {
    apply(fact: OriginFact): GraphEffect[] {
        // 起源关系：src 是 dst 的起源，可能表示类型继承或来源
        return [{ kind: "addEdge", from: fact.src, to: fact.dst, edgeType: "origin" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Origin"
    }
}

class AliasRule implements Rule {
    apply(fact: AliasFact): GraphEffect[] {
        // 别名关系：两个变量是别名，类型相同
        return [{ kind: "addEdge", from: fact.from, to: fact.to, edgeType: "sameType" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Alias"
    }
}