export class FactStore {
  facts: Fact[] = [];
  private index = new Map<Fact["kind"], Fact[]>();

  add(fact: Fact) {
    this.facts.push(fact);
    const k = fact.kind;
    if (!this.index.has(k)) this.index.set(k, []);
    this.index.get(k)!.push(fact);
  }

  all<K extends Fact["kind"]>(
    kind: K
  ): Extract<Fact, { kind: K }>[] {
    return (this.index.get(kind) ?? []) as any;
  }
}

export type VarId = number;
export type TypeId = number;

export interface FlowFact {
  kind: "Flow";
  from: VarId;
  to: VarId;
  reason?: string;
}

export interface AnnotFact {
  kind: "Annot";
  target: VarId;
  type: VarId;
}

export interface UnaryOpFact {
  kind: "UnaryOp";
  operator: string;
  operand: VarId;
  result: VarId;
}

export interface BinaryOpFact {
  kind: "BinaryOp";
  operator: string;
  left: VarId;
  right: VarId;
  result: VarId;
}

export interface TernaryOpFact {
  kind: "TernaryOp";
  condition: VarId;
  true: VarId;
  false: VarId;
  result: VarId;
}

export interface AllocObjFact {
  kind: "AllocObj";
  varId: VarId;
}

export interface ReturnStmtFact {
  kind: "ReturnStmt";
  funcVarId: VarId;
  returnVarId: VarId;
}

export interface ParamFact {
  kind: "Param";
  funcVarId: VarId;
  paramVarId: VarId;
  paramIdx: number;
}

export interface ArgFact {
  kind: "Arg";
  funcVarId: VarId;
  argVarId: VarId;
  argIdx: number;
}

export interface ReturnAnnotFact {
  kind: "ReturnAnnot";
  funcVarId: VarId;
  typeVarId: VarId;
}

export interface ReturnVoidFact {
  kind: "ReturnVoid";
  funcVarId: VarId;
}

export interface AliasFact {
  kind: "Alias";
  from: VarId;
  to: VarId;
}

export interface PropFact {
  kind: "Prop";
  objVarId: VarId;
  propVarId: VarId;
}

export interface AllocEnumFact {
  kind: "AllocEnum";
  varId: VarId;
}

export interface EnumMemberFact {
  kind: "EnumMember";
  enumVarId: VarId;
  memberVarId: VarId;
}

export interface AllocFunctionFact {
  kind: "AllocFunction";
  varId: VarId;
  bind: VarId;
}

export interface AllocInterfaceFact {
  kind: "AllocInterface";
  varId: VarId;
}

export interface AllocClassFact {
  kind: "AllocClass";
  varId: VarId;
}

export interface AllocPrimitiveFact {
  kind: "AllocPrimitive";
  varId: VarId;
  typeId: TypeId;
}

export interface AllocLiteralFact {
  kind: "AllocLiteral";
  varId: VarId;
  value: string | number | boolean | null | bigint | RegExp;
  typeId: TypeId;
}

export interface AllocArrayFact {
  kind: "AllocArray";
  varId: VarId;
}

export interface ArrayElementFact {
  kind: "ArrayElement";
  arrayVarId: VarId;
  elementVarId: VarId;
}

export interface OriginFact {
  kind: "Origin";
  src: VarId;
  dst: VarId;
}

export interface NewInstanceFact {
  kind: "NewInstance";
  classVarId: VarId;
  instanceVarId: VarId;
}

export interface SameIDFact {  
  kind: "SameID";
  source: VarId;
  target: VarId;
}

export interface CallFact {
  kind: "Call";
  func: VarId;
  result: VarId;
}



/** 所有 Fact 的联合类型 */
export type Fact =
  | FlowFact
  | AnnotFact
  | ReturnAnnotFact
  | UnaryOpFact
  | BinaryOpFact
  | TernaryOpFact
  | AllocObjFact
  | ReturnStmtFact
  | ParamFact
  | ArgFact
  | ReturnVoidFact
  | AliasFact
  | PropFact
  | AllocEnumFact
  | EnumMemberFact
  | AllocFunctionFact
  | AllocInterfaceFact
  | AllocClassFact
  | AllocPrimitiveFact
  | AllocLiteralFact
  | AllocArrayFact
  | ArrayElementFact
  | OriginFact
  | NewInstanceFact
  | SameIDFact
  | CallFact
  ;


export class Emitter {
  constructor(private store: FactStore) {}

  flow(from: VarId, to: VarId, reason?: string) {
    this.store.add({ kind: "Flow", from, to, reason });
  }

  annot(target: VarId, type: VarId) {
    this.store.add({ kind: "Annot", target, type });
  }

  returnAnnot(funcVarId: VarId, typeVarId: VarId) {
    this.store.add({ kind: "ReturnAnnot", funcVarId, typeVarId });
  }

  unaryOp(op: UnaryOpFact["operator"], operand: VarId, result: VarId) {
    this.store.add({ kind: "UnaryOp", operator: op, operand,  result });
  }

  binaryOp(op: BinaryOpFact["operator"], left: VarId, right: VarId, result: VarId) {
    this.store.add({ kind: "BinaryOp", operator: op, left, right, result });
  }

  ternaryOp(condition: VarId, trueVar: VarId, falseVar: VarId, result: VarId) {
    this.store.add({ kind: "TernaryOp", condition, true: trueVar, false: falseVar, result });
  }

  allocObj(varId: VarId) {
    this.store.add({ kind: "AllocObj", varId });
  }

  returnStmt(funcVarId: VarId, returnVarId: VarId) {
    this.store.add({ kind: "ReturnStmt", funcVarId, returnVarId });
  }

  param(funcVarId: VarId, paramVarId: VarId, paramIdx: number) {
    this.store.add({ kind: "Param", funcVarId, paramVarId, paramIdx });
  }

  arg(funcVarId: VarId, argVarId: VarId, argIdx: number) {
    this.store.add({ kind: "Arg", funcVarId, argVarId, argIdx });
  }

  returnVoid(funcVarId: VarId) {
    this.store.add({ kind: "ReturnVoid", funcVarId });
  }

  alias(from: VarId, to: VarId) {
    this.store.add({ kind: "Alias", from, to });
  }

  prop(objVarId: VarId, propVarId: VarId) {
    this.store.add({ kind: "Prop", objVarId, propVarId });
  }

  allocEnum(varId: VarId) {
    this.store.add({ kind: "AllocEnum", varId });
  }

  enumMember(enumVarId: VarId, memberVarId: VarId) {
    this.store.add({ kind: "EnumMember", enumVarId, memberVarId });
  }

  allocFunction(varId: VarId, bind: VarId) {
    this.store.add({ kind: "AllocFunction", varId, bind});
  }

  allocInterface(varId: VarId) {
    this.store.add({ kind: "AllocInterface", varId });
  }

  allocClass(varId: VarId) {
    this.store.add({ kind: "AllocClass", varId });
  }

  allocPrimitive(varId: VarId, typeId: TypeId) {
    this.store.add({ kind: "AllocPrimitive", varId, typeId });
  }

  allocLiteral(varId: VarId, value: string | number | boolean | null | bigint | RegExp, typeId: TypeId) {
    this.store.add({ kind: "AllocLiteral", varId, value, typeId });
  }

  allocArray(varId: VarId) {  
    this.store.add({ kind: "AllocArray", varId });
  }

  arrayElement(arrayVarId: VarId, elementVarId: VarId) {
    this.store.add({ kind: "ArrayElement", arrayVarId, elementVarId });
  }

  origin(src: VarId, dst: VarId) {
    this.store.add({ kind: "Origin", src, dst });
  }

  newinstance(classVarId: VarId, instanceVarId: VarId) {  
    this.store.add({ kind: "NewInstance", classVarId, instanceVarId });
  }

  sameID(source: VarId, target: VarId) {
    this.store.add({ kind: "SameID", source, target });
  }

  call(func: VarId, result: VarId) {
    this.store.add({ kind: "Call", func, result });
  }
}