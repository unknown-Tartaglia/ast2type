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
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
var Visitor = /*#__PURE__*/function () {
  function Visitor() {
    _classCallCheck(this, Visitor);
  }
  return _createClass(Visitor, [{
    key: "visitProgram",
    value: function visitProgram(node) {
      var _iterator = _createForOfIteratorHelper(node.topLevelStatements),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var statement = _step.value;
          statement.visit(this);
        }
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
    }
  }, {
    key: "visitFunc",
    value: function visitFunc(node) {
      node.returnType.visit(this);
      var _iterator2 = _createForOfIteratorHelper(node.typeParameters),
        _step2;
      try {
        for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
          var typeParameter = _step2.value;
          typeParameter.visit(this);
        }
      } catch (err) {
        _iterator2.e(err);
      } finally {
        _iterator2.f();
      }
      var _iterator3 = _createForOfIteratorHelper(node.parameters),
        _step3;
      try {
        for (_iterator3.s(); !(_step3 = _iterator3.n()).done;) {
          var parameter = _step3.value;
          parameter.visit(this);
        }
      } catch (err) {
        _iterator3.e(err);
      } finally {
        _iterator3.f();
      }
    }
  }, {
    key: "visitProtocolFuncDecl",
    value: function visitProtocolFuncDecl(node) {
      this.visitFunc(node);
    }
  }, {
    key: "visitFuncParameter",
    value: function visitFuncParameter(node) {
      node.type.visit(this);
    }
  }, {
    key: "visitFuncDef",
    value: function visitFuncDef(node) {
      this.visitFunc(node);
      node.body.visit(this);
    }
  }, {
    key: "visitNativeFunc",
    value: function visitNativeFunc(node) {
      this.visitFunc(node);
    }
  }, {
    key: "visitNativeFuncInstance",
    value: function visitNativeFuncInstance(node) {
      this.visitFunc(node);
      node.func.visitImplementationData(node.implementationData, this);
    }
  }, {
    key: "visitBlock",
    value: function visitBlock(node) {
      var _iterator4 = _createForOfIteratorHelper(node.statements),
        _step4;
      try {
        for (_iterator4.s(); !(_step4 = _iterator4.n()).done;) {
          var statement = _step4.value;
          statement.visit(this);
        }
      } catch (err) {
        _iterator4.e(err);
      } finally {
        _iterator4.f();
      }
    }
  }, {
    key: "visitCommaExpression",
    value: function visitCommaExpression(node) {
      var _iterator5 = _createForOfIteratorHelper(node.list),
        _step5;
      try {
        for (_iterator5.s(); !(_step5 = _iterator5.n()).done;) {
          var expression = _step5.value;
          expression.visit(this);
        }
      } catch (err) {
        _iterator5.e(err);
      } finally {
        _iterator5.f();
      }
    }
  }, {
    key: "visitProtocolRef",
    value: function visitProtocolRef(node) {}
  }, {
    key: "visitProtocolDecl",
    value: function visitProtocolDecl(node) {
      var _iterator6 = _createForOfIteratorHelper(node.extends),
        _step6;
      try {
        for (_iterator6.s(); !(_step6 = _iterator6.n()).done;) {
          var protocol = _step6.value;
          protocol.visit(this);
        }
      } catch (err) {
        _iterator6.e(err);
      } finally {
        _iterator6.f();
      }
      var _iterator7 = _createForOfIteratorHelper(node.signatures),
        _step7;
      try {
        for (_iterator7.s(); !(_step7 = _iterator7.n()).done;) {
          var signature = _step7.value;
          signature.visit(this);
        }
      } catch (err) {
        _iterator7.e(err);
      } finally {
        _iterator7.f();
      }
    }
  }, {
    key: "visitTypeRef",
    value: function visitTypeRef(node) {
      var _iterator8 = _createForOfIteratorHelper(node.typeArguments),
        _step8;
      try {
        for (_iterator8.s(); !(_step8 = _iterator8.n()).done;) {
          var typeArgument = _step8.value;
          typeArgument.visit(this);
        }
      } catch (err) {
        _iterator8.e(err);
      } finally {
        _iterator8.f();
      }
    }
  }, {
    key: "visitNativeType",
    value: function visitNativeType(node) {
      var _iterator9 = _createForOfIteratorHelper(node.typeParameters),
        _step9;
      try {
        for (_iterator9.s(); !(_step9 = _iterator9.n()).done;) {
          var typeParameter = _step9.value;
          typeParameter.visit(this);
        }
      } catch (err) {
        _iterator9.e(err);
      } finally {
        _iterator9.f();
      }
    }
  }, {
    key: "visitNativeTypeInstance",
    value: function visitNativeTypeInstance(node) {
      node.type.visit(this);
      var _iterator0 = _createForOfIteratorHelper(node.typeArguments),
        _step0;
      try {
        for (_iterator0.s(); !(_step0 = _iterator0.n()).done;) {
          var typeArgument = _step0.value;
          typeArgument.visit(this);
        }
      } catch (err) {
        _iterator0.e(err);
      } finally {
        _iterator0.f();
      }
    }
  }, {
    key: "visitTypeDef",
    value: function visitTypeDef(node) {
      var _iterator1 = _createForOfIteratorHelper(node.typeParameters),
        _step1;
      try {
        for (_iterator1.s(); !(_step1 = _iterator1.n()).done;) {
          var typeParameter = _step1.value;
          typeParameter.visit(this);
        }
      } catch (err) {
        _iterator1.e(err);
      } finally {
        _iterator1.f();
      }
      node.type.visit(this);
    }
  }, {
    key: "visitStructType",
    value: function visitStructType(node) {
      var _iterator10 = _createForOfIteratorHelper(node.typeParameters),
        _step10;
      try {
        for (_iterator10.s(); !(_step10 = _iterator10.n()).done;) {
          var typeParameter = _step10.value;
          typeParameter.visit(this);
        }
      } catch (err) {
        _iterator10.e(err);
      } finally {
        _iterator10.f();
      }
      var _iterator11 = _createForOfIteratorHelper(node.fields),
        _step11;
      try {
        for (_iterator11.s(); !(_step11 = _iterator11.n()).done;) {
          var field = _step11.value;
          field.visit(this);
        }
      } catch (err) {
        _iterator11.e(err);
      } finally {
        _iterator11.f();
      }
    }
  }, {
    key: "visitTypeVariable",
    value: function visitTypeVariable(node) {
      Node.visit(node.protocol, this);
    }
  }, {
    key: "visitConstexprTypeParameter",
    value: function visitConstexprTypeParameter(node) {
      node.type.visit(this);
    }
  }, {
    key: "visitField",
    value: function visitField(node) {
      node.type.visit(this);
    }
  }, {
    key: "visitEnumType",
    value: function visitEnumType(node) {
      node.baseType.visit(this);
      var _iterator12 = _createForOfIteratorHelper(node.members),
        _step12;
      try {
        for (_iterator12.s(); !(_step12 = _iterator12.n()).done;) {
          var member = _step12.value;
          member.visit(this);
        }
      } catch (err) {
        _iterator12.e(err);
      } finally {
        _iterator12.f();
      }
    }
  }, {
    key: "visitEnumMember",
    value: function visitEnumMember(node) {
      Node.visit(node.value, this);
    }
  }, {
    key: "visitEnumLiteral",
    value: function visitEnumLiteral(node) {}
  }, {
    key: "visitElementalType",
    value: function visitElementalType(node) {
      node.elementType.visit(this);
    }
  }, {
    key: "visitReferenceType",
    value: function visitReferenceType(node) {
      this.visitElementalType(node);
    }
  }, {
    key: "visitPtrType",
    value: function visitPtrType(node) {
      this.visitReferenceType(node);
    }
  }, {
    key: "visitArrayRefType",
    value: function visitArrayRefType(node) {
      this.visitReferenceType(node);
    }
  }, {
    key: "visitArrayType",
    value: function visitArrayType(node) {
      this.visitElementalType(node);
      node.numElements.visit(this);
    }
  }, {
    key: "visitVariableDecl",
    value: function visitVariableDecl(node) {
      node.type.visit(this);
      Node.visit(node.initializer, this);
    }
  }, {
    key: "visitAssignment",
    value: function visitAssignment(node) {
      node.lhs.visit(this);
      node.rhs.visit(this);
      Node.visit(node.type, this);
    }
  }, {
    key: "visitReadModifyWriteExpression",
    value: function visitReadModifyWriteExpression(node) {
      node.lValue.visit(this);
      node.oldValueVar.visit(this);
      node.newValueVar.visit(this);
      node.newValueExp.visit(this);
      node.resultExp.visit(this);
    }
  }, {
    key: "visitDereferenceExpression",
    value: function visitDereferenceExpression(node) {
      node.ptr.visit(this);
    }
  }, {
    key: "_handlePropertyAccessExpression",
    value: function _handlePropertyAccessExpression(node) {
      Node.visit(node.baseType, this);
      Node.visit(node.callForGet, this);
      Node.visit(node.resultTypeForGet, this);
      Node.visit(node.callForAnd, this);
      Node.visit(node.resultTypeForAnd, this);
      Node.visit(node.callForSet, this);
    }
  }, {
    key: "visitDotExpression",
    value: function visitDotExpression(node) {
      node.struct.visit(this);
      this._handlePropertyAccessExpression(node);
    }
  }, {
    key: "visitIndexExpression",
    value: function visitIndexExpression(node) {
      node.array.visit(this);
      node.index.visit(this);
      this._handlePropertyAccessExpression(node);
    }
  }, {
    key: "visitMakePtrExpression",
    value: function visitMakePtrExpression(node) {
      node.lValue.visit(this);
    }
  }, {
    key: "visitMakeArrayRefExpression",
    value: function visitMakeArrayRefExpression(node) {
      node.lValue.visit(this);
      Node.visit(node.numElements, this);
    }
  }, {
    key: "visitConvertPtrToArrayRefExpression",
    value: function visitConvertPtrToArrayRefExpression(node) {
      node.lValue.visit(this);
    }
  }, {
    key: "visitVariableRef",
    value: function visitVariableRef(node) {}
  }, {
    key: "visitIfStatement",
    value: function visitIfStatement(node) {
      node.conditional.visit(this);
      node.body.visit(this);
      Node.visit(node.elseBody, this);
    }
  }, {
    key: "visitWhileLoop",
    value: function visitWhileLoop(node) {
      node.conditional.visit(this);
      node.body.visit(this);
    }
  }, {
    key: "visitDoWhileLoop",
    value: function visitDoWhileLoop(node) {
      node.body.visit(this);
      node.conditional.visit(this);
    }
  }, {
    key: "visitForLoop",
    value: function visitForLoop(node) {
      Node.visit(node.initialization, this);
      Node.visit(node.condition, this);
      Node.visit(node.increment, this);
      node.body.visit(this);
    }
  }, {
    key: "visitSwitchStatement",
    value: function visitSwitchStatement(node) {
      node.value.visit(this);
      var _iterator13 = _createForOfIteratorHelper(node.switchCases),
        _step13;
      try {
        for (_iterator13.s(); !(_step13 = _iterator13.n()).done;) {
          var switchCase = _step13.value;
          switchCase.visit(this);
        }
      } catch (err) {
        _iterator13.e(err);
      } finally {
        _iterator13.f();
      }
    }
  }, {
    key: "visitSwitchCase",
    value: function visitSwitchCase(node) {
      Node.visit(node.value, this);
      node.body.visit(this);
    }
  }, {
    key: "visitReturn",
    value: function visitReturn(node) {
      Node.visit(node.value, this);
    }
  }, {
    key: "visitContinue",
    value: function visitContinue(node) {}
  }, {
    key: "visitBreak",
    value: function visitBreak(node) {}
  }, {
    key: "visitTrapStatement",
    value: function visitTrapStatement(node) {}
  }, {
    key: "visitGenericLiteral",
    value: function visitGenericLiteral(node) {
      node.type.visit(this);
    }
  }, {
    key: "visitGenericLiteralType",
    value: function visitGenericLiteralType(node) {
      Node.visit(node.type, this);
      node.preferredType.visit(this);
    }
  }, {
    key: "visitNullLiteral",
    value: function visitNullLiteral(node) {
      node.type.visit(this);
    }
  }, {
    key: "visitBoolLiteral",
    value: function visitBoolLiteral(node) {}
  }, {
    key: "visitNullType",
    value: function visitNullType(node) {
      Node.visit(node.type, this);
    }
  }, {
    key: "visitCallExpression",
    value: function visitCallExpression(node) {
      var _this = this;
      var _iterator14 = _createForOfIteratorHelper(node.typeArguments),
        _step14;
      try {
        for (_iterator14.s(); !(_step14 = _iterator14.n()).done;) {
          var typeArgument = _step14.value;
          typeArgument.visit(this);
        }
      } catch (err) {
        _iterator14.e(err);
      } finally {
        _iterator14.f();
      }
      var _iterator15 = _createForOfIteratorHelper(node.argumentList),
        _step15;
      try {
        for (_iterator15.s(); !(_step15 = _iterator15.n()).done;) {
          var argument = _step15.value;
          Node.visit(argument, this);
        }
      } catch (err) {
        _iterator15.e(err);
      } finally {
        _iterator15.f();
      }
      var handleTypeArguments = function handleTypeArguments(actualTypeArguments) {
        if (actualTypeArguments) {
          var _iterator16 = _createForOfIteratorHelper(actualTypeArguments),
            _step16;
          try {
            for (_iterator16.s(); !(_step16 = _iterator16.n()).done;) {
              var argument = _step16.value;
              argument.visit(_this);
            }
          } catch (err) {
            _iterator16.e(err);
          } finally {
            _iterator16.f();
          }
        }
      };
      handleTypeArguments(node.actualTypeArguments);
      handleTypeArguments(node.instantiatedActualTypeArguments);
      Node.visit(node.nativeFuncInstance, this);
      Node.visit(node.returnType, this);
      Node.visit(node.resultType, this);
    }
  }, {
    key: "visitLogicalNot",
    value: function visitLogicalNot(node) {
      node.operand.visit(this);
    }
  }, {
    key: "visitLogicalExpression",
    value: function visitLogicalExpression(node) {
      node.left.visit(this);
      node.right.visit(this);
    }
  }, {
    key: "visitFunctionLikeBlock",
    value: function visitFunctionLikeBlock(node) {
      Node.visit(node.returnType, this);
      var _iterator17 = _createForOfIteratorHelper(node.argumentList),
        _step17;
      try {
        for (_iterator17.s(); !(_step17 = _iterator17.n()).done;) {
          var argument = _step17.value;
          argument.visit(this);
        }
      } catch (err) {
        _iterator17.e(err);
      } finally {
        _iterator17.f();
      }
      var _iterator18 = _createForOfIteratorHelper(node.parameters),
        _step18;
      try {
        for (_iterator18.s(); !(_step18 = _iterator18.n()).done;) {
          var parameter = _step18.value;
          parameter.visit(this);
        }
      } catch (err) {
        _iterator18.e(err);
      } finally {
        _iterator18.f();
      }
      node.body.visit(this);
      Node.visit(node.resultType, this);
    }
  }, {
    key: "visitAnonymousVariable",
    value: function visitAnonymousVariable(node) {
      Node.visit(node.type, this);
    }
  }, {
    key: "visitIdentityExpression",
    value: function visitIdentityExpression(node) {
      node.target.visit(this);
    }
  }]);
}();