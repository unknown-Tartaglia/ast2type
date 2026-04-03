/*
 * Copyright (C) 2017 Apple Inc. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY APPLE INC. ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL APPLE INC. OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY
 * OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. 
 */
"use strict";

function _typeof(o) { "@babel/helpers - typeof"; return _typeof = "function" == typeof Symbol && "symbol" == typeof Symbol.iterator ? function (o) { return typeof o; } : function (o) { return o && "function" == typeof Symbol && o.constructor === Symbol && o !== Symbol.prototype ? "symbol" : typeof o; }, _typeof(o); }
function _toConsumableArray(r) { return _arrayWithoutHoles(r) || _iterableToArray(r) || _unsupportedIterableToArray(r) || _nonIterableSpread(); }
function _nonIterableSpread() { throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); }
function _iterableToArray(r) { if ("undefined" != typeof Symbol && null != r[Symbol.iterator] || null != r["@@iterator"]) return Array.from(r); }
function _arrayWithoutHoles(r) { if (Array.isArray(r)) return _arrayLikeToArray(r); }
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
function _callSuper(t, o, e) { return o = _getPrototypeOf(o), _possibleConstructorReturn(t, _isNativeReflectConstruct() ? Reflect.construct(o, e || [], _getPrototypeOf(t).constructor) : o.apply(t, e)); }
function _possibleConstructorReturn(t, e) { if (e && ("object" == _typeof(e) || "function" == typeof e)) return e; if (void 0 !== e) throw new TypeError("Derived constructors may only return object or undefined"); return _assertThisInitialized(t); }
function _assertThisInitialized(e) { if (void 0 === e) throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); return e; }
function _isNativeReflectConstruct() { try { var t = !Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], function () {})); } catch (t) {} return (_isNativeReflectConstruct = function _isNativeReflectConstruct() { return !!t; })(); }
function _getPrototypeOf(t) { return _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function (t) { return t.__proto__ || Object.getPrototypeOf(t); }, _getPrototypeOf(t); }
function _inherits(t, e) { if ("function" != typeof e && null !== e) throw new TypeError("Super expression must either be null or a function"); t.prototype = Object.create(e && e.prototype, { constructor: { value: t, writable: !0, configurable: !0 } }), Object.defineProperty(t, "prototype", { writable: !1 }), e && _setPrototypeOf(t, e); }
function _setPrototypeOf(t, e) { return _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function (t, e) { return t.__proto__ = e, t; }, _setPrototypeOf(t, e); }
var Checker = /*#__PURE__*/function (_Visitor) {
  function Checker(program) {
    var _this;
    _classCallCheck(this, Checker);
    _this = _callSuper(this, Checker);
    _this._program = program;
    _this._currentStatement = null;
    _this._vertexEntryPoints = new Set();
    _this._fragmentEntryPoints = new Set();
    return _this;
  }
  _inherits(Checker, _Visitor);
  return _createClass(Checker, [{
    key: "visitProgram",
    value: function visitProgram(node) {
      var _this2 = this;
      var doStatement = function doStatement(statement) {
        _this2._currentStatement = statement;
        statement.visit(_this2);
      };
      var _iterator = _createForOfIteratorHelper(node.types.values()),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var type = _step.value;
          doStatement(type);
        }
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
      var _iterator2 = _createForOfIteratorHelper(node.protocols.values()),
        _step2;
      try {
        for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
          var protocol = _step2.value;
          doStatement(protocol);
        }
      } catch (err) {
        _iterator2.e(err);
      } finally {
        _iterator2.f();
      }
      var _iterator3 = _createForOfIteratorHelper(node.functions.values()),
        _step3;
      try {
        for (_iterator3.s(); !(_step3 = _iterator3.n()).done;) {
          var funcs = _step3.value;
          var _iterator5 = _createForOfIteratorHelper(funcs),
            _step5;
          try {
            for (_iterator5.s(); !(_step5 = _iterator5.n()).done;) {
              var func = _step5.value;
              this.visitFunc(func);
            }
          } catch (err) {
            _iterator5.e(err);
          } finally {
            _iterator5.f();
          }
        }
      } catch (err) {
        _iterator3.e(err);
      } finally {
        _iterator3.f();
      }
      var _iterator4 = _createForOfIteratorHelper(node.functions.values()),
        _step4;
      try {
        for (_iterator4.s(); !(_step4 = _iterator4.n()).done;) {
          var _funcs = _step4.value;
          var _iterator6 = _createForOfIteratorHelper(_funcs),
            _step6;
          try {
            for (_iterator6.s(); !(_step6 = _iterator6.n()).done;) {
              var _func = _step6.value;
              doStatement(_func);
            }
          } catch (err) {
            _iterator6.e(err);
          } finally {
            _iterator6.f();
          }
        }
      } catch (err) {
        _iterator4.e(err);
      } finally {
        _iterator4.f();
      }
    }
  }, {
    key: "_checkShaderType",
    value: function _checkShaderType(node) {
      // FIXME: Relax these checks once we have implemented support for textures and samplers.
      if (node.typeParameters.length != 0) throw new WTypeError(node.origin.originString, "Entry point " + node.name + " must not have type arguments.");
      var shaderFunc = node;
      switch (node.shaderType) {
        case "vertex":
          if (this._vertexEntryPoints.has(node.name)) throw new WTypeError(node.origin.originString, "Duplicate vertex entry point name " + node.name);
          this._vertexEntryPoints.add(node.name);
          break;
        case "fragment":
          if (this._fragmentEntryPoints.has(node.name)) throw new WTypeError(node.origin.originString, "Duplicate fragment entry point name " + node.name);
          this._fragmentEntryPoints.add(node.name);
          break;
      }
    }
  }, {
    key: "_checkOperatorOverload",
    value: function _checkOperatorOverload(func, resolveFuncs) {
      if (Lexer.textIsIdentifier(func.name)) return; // Not operator!

      if (!func.name.startsWith("operator")) throw new Error("Bad operator overload name: " + func.name);
      var typeVariableTracker = new TypeVariableTracker();
      var _iterator7 = _createForOfIteratorHelper(func.parameterTypes),
        _step7;
      try {
        for (_iterator7.s(); !(_step7 = _iterator7.n()).done;) {
          var parameterType = _step7.value;
          parameterType.visit(typeVariableTracker);
        }
      } catch (err) {
        _iterator7.e(err);
      } finally {
        _iterator7.f();
      }
      Node.visit(func.returnTypeForOverloadResolution, typeVariableTracker);
      var _iterator8 = _createForOfIteratorHelper(func.typeParameters),
        _step8;
      try {
        for (_iterator8.s(); !(_step8 = _iterator8.n()).done;) {
          var typeParameter = _step8.value;
          if (!typeVariableTracker.set.has(typeParameter)) throw new WTypeError(typeParameter.origin.originString, "Type parameter " + typeParameter + " to operator " + func.toDeclString() + " is not inferrable from value parameters");
        }
      } catch (err) {
        _iterator8.e(err);
      } finally {
        _iterator8.f();
      }
      var checkGetter = function checkGetter(kind) {
        var numExpectedParameters = kind == "index" ? 2 : 1;
        if (func.parameters.length != numExpectedParameters) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected " + numExpectedParameters + ", got " + func.parameters.length + ")");
        if (func.parameterTypes[0].unifyNode.isPtr) throw new WTypeError(func.origin.originString, "Cannot have getter for pointer type: " + func.parameterTypes[0]);
      };
      var checkSetter = function checkSetter(kind) {
        var numExpectedParameters = kind == "index" ? 3 : 2;
        if (func.parameters.length != numExpectedParameters) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected " + numExpectedParameters + ", got " + func.parameters.length + ")");
        if (func.parameterTypes[0].unifyNode.isPtr) throw new WTypeError(func.origin.originString, "Cannot have setter for pointer type: " + func.parameterTypes[0]);
        if (!func.returnType.equals(func.parameterTypes[0])) throw new WTypeError(func.origin.originString, "First parameter type and return type of setter must match (parameter was " + func.parameterTypes[0] + " but return was " + func.returnType + ")");
        var valueType = func.parameterTypes[numExpectedParameters - 1];
        var getterName = func.name.substr(0, func.name.length - 1);
        var getterFuncs = resolveFuncs(getterName);
        if (!getterFuncs) throw new WTypeError(func.origin.originString, "Every setter must have a matching getter, but did not find any function named " + getterName + " to match " + func.name);
        var argumentTypes = func.parameterTypes.slice(0, numExpectedParameters - 1);
        var overload = resolveOverloadImpl(getterFuncs, [], argumentTypes, null);
        if (!overload.func) throw new WTypeError(func.origin.originString, "Did not find function named " + func.name + " with arguments " + argumentTypes + (overload.failures.length ? "; tried:\n" + overload.failures.join("\n") : ""));
        var resultType = overload.func.returnType.substituteToUnification(overload.func.typeParameters, overload.unificationContext);
        if (!resultType.equals(valueType)) throw new WTypeError(func.origin.originString, "Setter and getter must agree on value type (getter at " + overload.func.origin.originString + " says " + resultType + " while this setter says " + valueType + ")");
      };
      var checkAnder = function checkAnder(kind) {
        var numExpectedParameters = kind == "index" ? 2 : 1;
        if (func.parameters.length != numExpectedParameters) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected " + numExpectedParameters + ", got " + func.parameters.length + ")");
        if (!func.returnType.unifyNode.isPtr) throw new WTypeError(func.origin.originString, "Return type of ander is not a pointer: " + func.returnType);
        if (!func.parameterTypes[0].unifyNode.isRef) throw new WTypeError(func.origin.originString, "Parameter to ander is not a reference: " + func.parameterTypes[0]);
      };
      switch (func.name) {
        case "operator cast":
          break;
        case "operator++":
        case "operator--":
          if (func.parameters.length != 1) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected 1, got " + func.parameters.length + ")");
          if (!func.parameterTypes[0].equals(func.returnType)) throw new WTypeError(func.origin.originString, "Parameter type and return type must match for " + func.name + " (parameter is " + func.parameterTypes[0] + " while return is " + func.returnType + ")");
          break;
        case "operator+":
        case "operator-":
          if (func.parameters.length != 1 && func.parameters.length != 2) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected 1 or 2, got " + func.parameters.length + ")");
          break;
        case "operator*":
        case "operator/":
        case "operator%":
        case "operator&":
        case "operator|":
        case "operator^":
        case "operator<<":
        case "operator>>":
          if (func.parameters.length != 2) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected 2, got " + func.parameters.length + ")");
          break;
        case "operator~":
          if (func.parameters.length != 1) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected 1, got " + func.parameters.length + ")");
          break;
        case "operator==":
        case "operator<":
        case "operator<=":
        case "operator>":
        case "operator>=":
          if (func.parameters.length != 2) throw new WTypeError(func.origin.originString, "Incorrect number of parameters for " + func.name + " (expected 2, got " + func.parameters.length + ")");
          if (!func.returnType.equals(this._program.intrinsics.bool)) throw new WTypeError(func.origin.originString, "Return type of " + func.name + " must be bool but was " + func.returnType);
          break;
        case "operator[]":
          checkGetter("index");
          break;
        case "operator[]=":
          checkSetter("index");
          break;
        case "operator&[]":
          checkAnder("index");
          break;
        default:
          if (func.name.startsWith("operator.")) {
            if (func.name.endsWith("=")) checkSetter("dot");else checkGetter("dot");
            break;
          }
          if (func.name.startsWith("operator&.")) {
            checkAnder("dot");
            break;
          }
          throw new Error("Parser accepted unrecognized operator: " + func.name);
      }
    }
  }, {
    key: "visitFuncDef",
    value: function visitFuncDef(node) {
      var _this3 = this;
      if (node.shaderType) this._checkShaderType(node);
      this._checkOperatorOverload(node, function (name) {
        return _this3._program.functions.get(name);
      });
      node.body.visit(this);
    }
  }, {
    key: "visitNativeFunc",
    value: function visitNativeFunc(node) {}
  }, {
    key: "visitProtocolDecl",
    value: function visitProtocolDecl(node) {
      var _iterator9 = _createForOfIteratorHelper(node.signatures),
        _step9;
      try {
        for (_iterator9.s(); !(_step9 = _iterator9.n()).done;) {
          var signature = _step9.value;
          var typeVariableTracker = new TypeVariableTracker();
          var _iterator0 = _createForOfIteratorHelper(signature.parameterTypes),
            _step0;
          try {
            for (_iterator0.s(); !(_step0 = _iterator0.n()).done;) {
              var parameterType = _step0.value;
              parameterType.visit(typeVariableTracker);
            }
          } catch (err) {
            _iterator0.e(err);
          } finally {
            _iterator0.f();
          }
          Node.visit(signature.returnTypeForOverloadResolution, typeVariableTracker);
          var _iterator1 = _createForOfIteratorHelper(signature.typeParameters),
            _step1;
          try {
            for (_iterator1.s(); !(_step1 = _iterator1.n()).done;) {
              var typeParameter = _step1.value;
              if (!typeVariableTracker.set.has(typeParameter)) throw WTypeError(typeParameter.origin.originString, "Type parameter to protocol signature not inferrable from value parameters");
            }
          } catch (err) {
            _iterator1.e(err);
          } finally {
            _iterator1.f();
          }
          if (!typeVariableTracker.set.has(node.typeVariable)) throw new WTypeError(signature.origin.originString, "Protocol's type variable (" + node.name + ") not mentioned in signature: " + signature);
          this._checkOperatorOverload(signature, function (name) {
            return node.signaturesByName(name);
          });
        }
      } catch (err) {
        _iterator9.e(err);
      } finally {
        _iterator9.f();
      }
    }
  }, {
    key: "visitEnumType",
    value: function visitEnumType(node) {
      node.baseType.visit(this);
      var baseType = node.baseType.unifyNode;
      if (!baseType.isInt) throw new WTypeError(node.origin.originString, "Base type of enum is not an integer: " + node.baseType);
      var _iterator10 = _createForOfIteratorHelper(node.members),
        _step10;
      try {
        for (_iterator10.s(); !(_step10 = _iterator10.n()).done;) {
          var _member = _step10.value;
          if (!_member.value) continue;
          var memberType = _member.value.visit(this);
          if (!baseType.equalsWithCommit(memberType)) throw new WTypeError(_member.origin.originString, "Type of enum member " + _member.value.name + " does not patch enum base type (member type is " + memberType + ", enum base type is " + node.baseType + ")");
        }
      } catch (err) {
        _iterator10.e(err);
      } finally {
        _iterator10.f();
      }
      var nextValue = baseType.defaultValue;
      var _iterator11 = _createForOfIteratorHelper(node.members),
        _step11;
      try {
        for (_iterator11.s(); !(_step11 = _iterator11.n()).done;) {
          var _member2 = _step11.value;
          if (_member2.value) {
            nextValue = baseType.successorValue(_member2.value.unifyNode.valueForSelectedType);
            continue;
          }
          _member2.value = baseType.createLiteral(_member2.origin, nextValue);
          nextValue = baseType.successorValue(nextValue);
        }
      } catch (err) {
        _iterator11.e(err);
      } finally {
        _iterator11.f();
      }
      var memberArray = Array.from(node.members);
      for (var i = 0; i < memberArray.length; ++i) {
        var member = memberArray[i];
        for (var j = i + 1; j < memberArray.length; ++j) {
          var otherMember = memberArray[j];
          if (baseType.valuesEqual(member.value.unifyNode.valueForSelectedType, otherMember.value.unifyNode.valueForSelectedType)) throw new WTypeError(otherMember.origin.originString, "Duplicate enum member value (" + member.name + " has " + member.value + " while " + otherMember.name + " has " + otherMember.value + ")");
        }
      }
      var foundZero = false;
      var _iterator12 = _createForOfIteratorHelper(node.members),
        _step12;
      try {
        for (_iterator12.s(); !(_step12 = _iterator12.n()).done;) {
          var _member3 = _step12.value;
          if (baseType.valuesEqual(_member3.value.unifyNode.valueForSelectedType, baseType.defaultValue)) {
            foundZero = true;
            break;
          }
        }
      } catch (err) {
        _iterator12.e(err);
      } finally {
        _iterator12.f();
      }
      if (!foundZero) throw new WTypeError(node.origin.originString, "Enum does not have a member with the value zero");
    }
  }, {
    key: "_checkTypeArguments",
    value: function _checkTypeArguments(origin, typeParameters, typeArguments) {
      for (var i = 0; i < typeParameters.length; ++i) {
        var argumentIsType = typeArguments[i] instanceof Type;
        var result = typeArguments[i].visit(this);
        if (argumentIsType) {
          var _result = typeArguments[i].inherits(typeParameters[i].protocol);
          if (!_result.result) throw new WTypeError(origin.originString, "Type argument does not inherit protocol: " + _result.reason);
        } else {
          if (!result.equalsWithCommit(typeParameters[i].type)) throw new WTypeError(origin.originString, "Wrong type for constexpr");
        }
      }
    }
  }, {
    key: "visitTypeRef",
    value: function visitTypeRef(node) {
      if (!node.type) throw new Error("Type reference without a type in checker: " + node + " at " + node.origin);
      if (!(node.type instanceof StructType)) node.type.visit(this);
      this._checkTypeArguments(node.origin, node.type.typeParameters, node.typeArguments);
    }
  }, {
    key: "visitArrayType",
    value: function visitArrayType(node) {
      node.elementType.visit(this);
      if (!node.numElements.isConstexpr) throw new WTypeError(node.origin.originString, "Array length must be constexpr");
      var type = node.numElements.visit(this);
      if (!type.equalsWithCommit(this._program.intrinsics.uint32)) throw new WTypeError(node.origin.originString, "Array length must be a uint32");
    }
  }, {
    key: "visitVariableDecl",
    value: function visitVariableDecl(node) {
      node.type.visit(this);
      if (node.initializer) {
        var lhsType = node.type;
        var rhsType = node.initializer.visit(this);
        if (!lhsType.equalsWithCommit(rhsType)) throw new WTypeError(node.origin.originString, "Type mismatch in variable initialization: " + lhsType + " versus " + rhsType);
      }
    }
  }, {
    key: "visitAssignment",
    value: function visitAssignment(node) {
      var lhsType = node.lhs.visit(this);
      if (!node.lhs.isLValue) throw new WTypeError(node.origin.originString, "LHS of assignment is not an LValue: " + node.lhs + node.lhs.notLValueReasonString);
      var rhsType = node.rhs.visit(this);
      if (!lhsType.equalsWithCommit(rhsType)) throw new WTypeError(node.origin.originString, "Type mismatch in assignment: " + lhsType + " versus " + rhsType);
      node.type = lhsType;
      return lhsType;
    }
  }, {
    key: "visitIdentityExpression",
    value: function visitIdentityExpression(node) {
      return node.target.visit(this);
    }
  }, {
    key: "visitReadModifyWriteExpression",
    value: function visitReadModifyWriteExpression(node) {
      var lhsType = node.lValue.visit(this);
      if (!node.lValue.isLValue) throw new WTypeError(node.origin.originString, "LHS of read-modify-write is not an LValue: " + node.lValue + node.lValue.notLValueReasonString);
      node.oldValueVar.type = lhsType;
      node.newValueVar.type = lhsType;
      node.oldValueVar.visit(this);
      node.newValueVar.visit(this);
      var newValueType = node.newValueExp.visit(this);
      if (!lhsType.equalsWithCommit(newValueType)) return new WTypeError(node.origin.originString, "Type mismatch in read-modify-write: " + lhsType + " versus " + newValueType);
      return node.resultExp.visit(this);
    }
  }, {
    key: "visitAnonymousVariable",
    value: function visitAnonymousVariable(node) {
      if (!node.type) throw new Error("Anonymous variable must know type before first appearance");
    }
  }, {
    key: "visitDereferenceExpression",
    value: function visitDereferenceExpression(node) {
      var type = node.ptr.visit(this).unifyNode;
      if (!type.isPtr) throw new WTypeError(node.origin.originString, "Type passed to dereference is not a pointer: " + type);
      node.type = type.elementType;
      node.addressSpace = type.addressSpace;
      if (!node.addressSpace) throw new Error("Null address space in type: " + type);
      return node.type;
    }
  }, {
    key: "visitMakePtrExpression",
    value: function visitMakePtrExpression(node) {
      var elementType = node.lValue.visit(this).unifyNode;
      if (!node.lValue.isLValue) throw new WTypeError(node.origin.originString, "Operand to & is not an LValue: " + node.lValue + node.lValue.notLValueReasonString);
      return new PtrType(node.origin, node.lValue.addressSpace, elementType);
    }
  }, {
    key: "visitMakeArrayRefExpression",
    value: function visitMakeArrayRefExpression(node) {
      var elementType = node.lValue.visit(this).unifyNode;
      if (elementType.isPtr) {
        node.become(new ConvertPtrToArrayRefExpression(node.origin, node.lValue));
        return new ArrayRefType(node.origin, elementType.addressSpace, elementType.elementType);
      }
      if (!node.lValue.isLValue) throw new WTypeError(node.origin.originString, "Operand to @ is not an LValue: " + node.lValue + node.lValue.notLValueReasonString);
      if (elementType.isArray) {
        node.numElements = elementType.numElements;
        elementType = elementType.elementType;
      } else node.numElements = UintLiteral.withType(node.origin, 1, this._program.intrinsics.uint32);
      return new ArrayRefType(node.origin, node.lValue.addressSpace, elementType);
    }
  }, {
    key: "visitConvertToArrayRefExpression",
    value: function visitConvertToArrayRefExpression(node) {
      throw new Error("Should not exist yet.");
    }
  }, {
    key: "_finishVisitingPropertyAccess",
    value: function _finishVisitingPropertyAccess(node, baseType, extraArgs, extraArgTypes) {
      baseType = baseType.visit(new AutoWrapper());
      node.baseType = baseType;

      // Such a type must exist. This may throw if it doesn't.
      var typeForAnd = baseType.argumentTypeForAndOverload(node.origin);
      if (!typeForAnd) throw new Error("Cannot get typeForAnd");
      var errorForGet;
      var errorForAnd;
      try {
        var result = CallExpression.resolve(node.origin, node.possibleGetOverloads, this._currentStatement.typeParameters, node.getFuncName, [], [node.base].concat(_toConsumableArray(extraArgs)), [baseType].concat(_toConsumableArray(extraArgTypes)), null);
        node.callForGet = result.call;
        node.resultTypeForGet = result.resultType;
      } catch (e) {
        if (!(e instanceof WTypeError)) throw e;
        errorForGet = e;
      }
      try {
        var baseForAnd = baseType.argumentForAndOverload(node.origin, node.base);
        var _result2 = CallExpression.resolve(node.origin, node.possibleAndOverloads, this._currentStatement.typeParameters, node.andFuncName, [], [baseForAnd].concat(_toConsumableArray(extraArgs)), [typeForAnd].concat(_toConsumableArray(extraArgTypes)), null);
        node.callForAnd = _result2.call;
        node.resultTypeForAnd = _result2.resultType.unifyNode.returnTypeFromAndOverload(node.origin);
      } catch (e) {
        if (!(e instanceof WTypeError)) throw e;
        errorForAnd = e;
      }
      if (!node.resultTypeForGet && !node.resultTypeForAnd) {
        throw new WTypeError(node.origin.originString, "Cannot resolve access; tried by-value:\n" + errorForGet.typeErrorMessage + "\n" + "and tried by-pointer:\n" + errorForAnd.typeErrorMessage);
      }
      if (node.resultTypeForGet && node.resultTypeForAnd && !node.resultTypeForGet.equals(node.resultTypeForAnd)) throw new WTypeError(node.origin.originString, "Result type resolved by-value (" + node.resultTypeForGet + ") does not match result type resolved by-pointer (" + node.resultTypeForAnd + ")");
      try {
        var _result3 = CallExpression.resolve(node.origin, node.possibleSetOverloads, this._currentStatement.typeParameters, node.setFuncName, [], [node.base].concat(_toConsumableArray(extraArgs), [null]), [baseType].concat(_toConsumableArray(extraArgTypes), [node.resultType]), null);
        node.callForSet = _result3.call;
        if (!_result3.resultType.equals(baseType)) throw new WTypeError(node.origin.originString, "Result type of setter " + _result3.call.func + " is not the base type " + baseType);
      } catch (e) {
        if (!(e instanceof WTypeError)) throw e;
        node.errorForSet = e;
      }

      // OK, now we need to determine if we are an lvalue. We are an lvalue if we can be assigned to. We can
      // be assigned to if we have an ander or setter. But it's weirder than that. We also need the base to be
      // an lvalue, except unless the base is an array reference.
      if (!node.callForAnd && !node.callForSet) {
        node.isLValue = false;
        node.notLValueReason = "Have neither ander nor setter. Tried setter:\n" + node.errorForSet.typeErrorMessage + "\n" + "and tried ander:\n" + errorForAnd.typeErrorMessage;
      } else if (!node.base.isLValue && !baseType.isArrayRef) {
        node.isLValue = false;
        node.notLValueReason = "Base of property access is neither a lvalue nor an array reference";
      } else {
        node.isLValue = true;
        node.addressSpace = node.base.isLValue ? node.base.addressSpace : baseType.addressSpace;
      }
      return node.resultType;
    }
  }, {
    key: "visitDotExpression",
    value: function visitDotExpression(node) {
      var structType = node.struct.visit(this).unifyNode;
      return this._finishVisitingPropertyAccess(node, structType, [], []);
    }
  }, {
    key: "visitIndexExpression",
    value: function visitIndexExpression(node) {
      var arrayType = node.array.visit(this).unifyNode;
      var indexType = node.index.visit(this);
      return this._finishVisitingPropertyAccess(node, arrayType, [node.index], [indexType]);
    }
  }, {
    key: "visitVariableRef",
    value: function visitVariableRef(node) {
      if (!node.variable.type) throw new Error("Variable has no type: " + node.variable);
      return node.variable.type;
    }
  }, {
    key: "visitReturn",
    value: function visitReturn(node) {
      if (node.value) {
        var resultType = node.value.visit(this);
        if (!resultType) throw new Error("Null result type from " + node.value);
        if (!node.func.returnType.equalsWithCommit(resultType)) throw new WTypeError(node.origin.originString, "Trying to return " + resultType + " in a function that returns " + node.func.returnType);
        return;
      }
      if (!node.func.returnType.equalsWithCommit(this._program.intrinsics.void)) throw new WTypeError(node.origin.originString, "Non-void function must return a value");
    }
  }, {
    key: "visitGenericLiteral",
    value: function visitGenericLiteral(node) {
      return node.type;
    }
  }, {
    key: "visitNullLiteral",
    value: function visitNullLiteral(node) {
      return node.type;
    }
  }, {
    key: "visitBoolLiteral",
    value: function visitBoolLiteral(node) {
      return this._program.intrinsics.bool;
    }
  }, {
    key: "visitEnumLiteral",
    value: function visitEnumLiteral(node) {
      return node.member.enumType;
    }
  }, {
    key: "_requireBool",
    value: function _requireBool(expression) {
      var type = expression.visit(this);
      if (!type) throw new Error("Expression has no type, but should be bool: " + expression);
      if (!type.equals(this._program.intrinsics.bool)) throw new WTypeError("Expression isn't a bool: " + expression);
    }
  }, {
    key: "visitLogicalNot",
    value: function visitLogicalNot(node) {
      this._requireBool(node.operand);
      return this._program.intrinsics.bool;
    }
  }, {
    key: "visitLogicalExpression",
    value: function visitLogicalExpression(node) {
      this._requireBool(node.left);
      this._requireBool(node.right);
      return this._program.intrinsics.bool;
    }
  }, {
    key: "visitIfStatement",
    value: function visitIfStatement(node) {
      this._requireBool(node.conditional);
      node.body.visit(this);
      if (node.elseBody) node.elseBody.visit(this);
    }
  }, {
    key: "visitWhileLoop",
    value: function visitWhileLoop(node) {
      this._requireBool(node.conditional);
      node.body.visit(this);
    }
  }, {
    key: "visitDoWhileLoop",
    value: function visitDoWhileLoop(node) {
      node.body.visit(this);
      this._requireBool(node.conditional);
    }
  }, {
    key: "visitForLoop",
    value: function visitForLoop(node) {
      if (node.initialization) node.initialization.visit(this);
      if (node.condition) this._requireBool(node.condition);
      if (node.increment) node.increment.visit(this);
      node.body.visit(this);
    }
  }, {
    key: "visitSwitchStatement",
    value: function visitSwitchStatement(node) {
      var type = node.value.visit(this).commit();
      if (!type.unifyNode.isInt && !(type.unifyNode instanceof EnumType)) throw new WTypeError(node.origin.originString, "Cannot switch on non-integer/non-enum type: " + type);
      node.type = type;
      var hasDefault = false;
      var _iterator13 = _createForOfIteratorHelper(node.switchCases),
        _step13;
      try {
        for (_iterator13.s(); !(_step13 = _iterator13.n()).done;) {
          var _switchCase = _step13.value;
          _switchCase.body.visit(this);
          if (_switchCase.isDefault) {
            hasDefault = true;
            continue;
          }
          if (!_switchCase.value.isConstexpr) throw new WTypeError(_switchCase.origin.originString, "Switch case not constexpr: " + _switchCase.value);
          var caseType = _switchCase.value.visit(this);
          if (!type.equalsWithCommit(caseType)) throw new WTypeError(_switchCase.origin.originString, "Switch case type does not match switch value type (case type is " + caseType + " but switch value type is " + type + ")");
        }
      } catch (err) {
        _iterator13.e(err);
      } finally {
        _iterator13.f();
      }
      for (var i = 0; i < node.switchCases.length; ++i) {
        var firstCase = node.switchCases[i];
        for (var j = i + 1; j < node.switchCases.length; ++j) {
          var secondCase = node.switchCases[j];
          if (firstCase.isDefault != secondCase.isDefault) continue;
          if (firstCase.isDefault) throw new WTypeError(secondCase.origin.originString, "Duplicate default case in switch statement");
          var valuesEqual = type.unifyNode.valuesEqual(firstCase.value.unifyNode.valueForSelectedType, secondCase.value.unifyNode.valueForSelectedType);
          if (valuesEqual) throw new WTypeError(secondCase.origin.originString, "Duplicate case in switch statement for value " + firstCase.value.unifyNode.valueForSelectedType);
        }
      }
      if (!hasDefault) {
        var includedValues = new Set();
        var _iterator14 = _createForOfIteratorHelper(node.switchCases),
          _step14;
        try {
          for (_iterator14.s(); !(_step14 = _iterator14.n()).done;) {
            var switchCase = _step14.value;
            includedValues.add(switchCase.value.unifyNode.valueForSelectedType);
          }
        } catch (err) {
          _iterator14.e(err);
        } finally {
          _iterator14.f();
        }
        var _iterator15 = _createForOfIteratorHelper(type.unifyNode.allValues()),
          _step15;
        try {
          for (_iterator15.s(); !(_step15 = _iterator15.n()).done;) {
            var _step15$value = _step15.value,
              value = _step15$value.value,
              name = _step15$value.name;
            if (!includedValues.has(value)) throw new WTypeError(node.origin.originString, "Value not handled by switch statement: " + name);
          }
        } catch (err) {
          _iterator15.e(err);
        } finally {
          _iterator15.f();
        }
      }
    }
  }, {
    key: "visitCommaExpression",
    value: function visitCommaExpression(node) {
      var result = null;
      var _iterator16 = _createForOfIteratorHelper(node.list),
        _step16;
      try {
        for (_iterator16.s(); !(_step16 = _iterator16.n()).done;) {
          var expression = _step16.value;
          result = expression.visit(this);
        }
      } catch (err) {
        _iterator16.e(err);
      } finally {
        _iterator16.f();
      }
      return result;
    }
  }, {
    key: "visitCallExpression",
    value: function visitCallExpression(node) {
      var _this4 = this;
      var typeArguments = node.typeArguments.map(function (typeArgument) {
        return typeArgument.visit(_this4);
      });
      var argumentTypes = node.argumentList.map(function (argument) {
        var newArgument = argument.visit(_this4);
        if (!newArgument) throw new Error("visitor returned null for " + argument);
        return newArgument.visit(new AutoWrapper());
      });
      node.argumentTypes = argumentTypes;
      if (node.returnType) node.returnType.visit(this);
      var result = node.resolve(node.possibleOverloads, this._currentStatement.typeParameters, typeArguments);
      return result;
    }
  }]);
}(Visitor);