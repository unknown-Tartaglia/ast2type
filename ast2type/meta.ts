import { VarId } from "./fact";
export class MetaStore {
  // ===== 基础信息（几乎所有节点都有）=====
  file = new Map<VarId, string>();
  pos = new Map<VarId, any>();
  offset = new Map<VarId, number>();
  kind = new Map<VarId, string>();
  text = new Map<VarId, string>();
  context = new Map<VarId, string>();

  // ===== 可选 feature =====
  v8Kind = new Map<VarId, string>();
  objectName = new Map<VarId, string>();
  className = new Map<VarId, string>();
  interfaceName = new Map<VarId, string>();
  propName = new Map<VarId, string>();
  enumName = new Map<VarId, string>();
  enumMemberName = new Map<VarId, string>();
  funcName = new Map<VarId, string>();
  paramName = new Map<VarId, string>();
  paramIndex = new Map<VarId, number>();
  funcParamMap = new Map<VarId, Map<number, VarId>>(); // funcVarId -> (paramIdx -> paramVarId)
  funcBindMap = new Map<VarId, VarId>(); // bindVarId -> funcVarId (标识符绑定到函数)
}