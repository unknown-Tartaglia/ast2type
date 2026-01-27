import { meta, tNode } from "../ast2type";
import { AllocArrayFact, AllocLiteralFact, AllocObjFact, ArrayElementFact, BinaryOpFact, CallFact, Fact, FlowFact, NewInstanceFact, PropFact, SameIDFact, TypeId, VarId } from "./fact"

// 规则工厂
export class RuleStore {
    private rules: Rule[] = [];
    
    constructor() {
      this.registerRules();
    }
    
    private registerRules(): void {
      this.rules.push(
        new FlowRule(),
        new BinaryOpRule(),
        new AllocObjRule(), 
        new PropRule(),
        new AllocLiteralRule(),
        new AllocArrayRule(),
        new ArrayElementRule(),
        new NewInstanceRule(),
        new SameIDRule(),
        new CallRule()
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

class FlowRule implements Rule {
    apply(fact: FlowFact): GraphEffect[] {
        return [{ kind: "addEdge", from: fact.from, to: fact.to, edgeType: "sameType"}]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Flow"
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
                return [{ kind: "addEdge", from: fact.left, to: fact.result, edgeType: "sameType" },
                        { kind: "addEdge", from: fact.right, to: fact.left, edgeType: "sameType" }];
            case "+":
            case "-":
            case "*":
            case "/":
            case "%":
            case "**":
                return [{ kind: "addEdge", from: fact.left, to: fact.result, edgeType: "sameType" },
                        { kind: "addEdge", from: fact.right, to: fact.result, edgeType: "sameType" }];
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
            case "~":
            case "<<":
            case ">>":
            case ">>>":
                return [{ kind: "addEdge", from: fact.left, to: fact.result, edgeType: "sameType" },
                        { kind: "addEdge", from: fact.right, to: fact.result, edgeType: "sameType" }];
            case "instanceof":
                // TODO
                return [];
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
        return [{ kind: "addEdge", from: fact.func, to: fact.result, edgeType: "returnEdge" }]
    }
    canHandle(fact: Fact): boolean {
        return fact.kind === "Call"
    }
}