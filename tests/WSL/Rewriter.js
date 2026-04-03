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

// FIXME: This should have sensible behavior when it encounters definitions that it cannot handle. Right
// now we are hackishly preventing this by wrapping things in TypeRef. That's probably wrong.
// https://bugs.webkit.org/show_bug.cgi?id=176208
function _typeof(o) { "@babel/helpers - typeof"; return _typeof = "function" == typeof Symbol && "symbol" == typeof Symbol.iterator ? function (o) { return typeof o; } : function (o) { return o && "function" == typeof Symbol && o.constructor === Symbol && o !== Symbol.prototype ? "symbol" : typeof o; }, _typeof(o); }
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
var Rewriter = /*#__PURE__*/function () {
  function Rewriter() {
    _classCallCheck(this, Rewriter);
    this._mapping = new Map();
  }
  return _createClass(Rewriter, [{
    key: "_mapNode",
    value: function _mapNode(oldItem, newItem) {
      this._mapping.set(oldItem, newItem);
      return newItem;
    }
  }, {
    key: "_getMapping",
    value: function _getMapping(oldItem) {
      var result = this._mapping.get(oldItem);
      if (result) return result;
      return oldItem;
    }

    // We return identity for anything that is not inside a function/struct body. When processing
    // function bodies, we only recurse into them and never out of them - for example if there is a
    // function call to another function then we don't rewrite the other function. This is how we stop
    // that.
  }, {
    key: "visitFuncDef",
    value: function visitFuncDef(node) {
      return node;
    }
  }, {
    key: "visitNativeFunc",
    value: function visitNativeFunc(node) {
      return node;
    }
  }, {
    key: "visitNativeFuncInstance",
    value: function visitNativeFuncInstance(node) {
      return node;
    }
  }, {
    key: "visitNativeType",
    value: function visitNativeType(node) {
      return node;
    }
  }, {
    key: "visitTypeDef",
    value: function visitTypeDef(node) {
      return node;
    }
  }, {
    key: "visitStructType",
    value: function visitStructType(node) {
      return node;
    }
  }, {
    key: "visitConstexprTypeParameter",
    value: function visitConstexprTypeParameter(node) {
      return node;
    }
  }, {
    key: "visitProtocolDecl",
    value: function visitProtocolDecl(node) {
      return node;
    }
  }, {
    key: "visitEnumType",
    value: function visitEnumType(node) {
      return node;
    }

    // This is almost wrong. We instantiate Func in Substitution in ProtocolDecl. Then, we end up
    // not rewriting type variables. I think that just works because not rewriting them there is OK.
    // Everywhere else, it's mandatory that we don't rewrite these because we always assume that
    // type variables are outside the scope of rewriting.
  }, {
    key: "visitTypeVariable",
    value: function visitTypeVariable(node) {
      return node;
    }
  }, {
    key: "visitProtocolFuncDecl",
    value: function visitProtocolFuncDecl(node) {
      var _this = this;
      var result = new ProtocolFuncDecl(node.origin, node.name, node.returnType.visit(this), node.typeParameters.map(function (parameter) {
        return parameter.visit(_this);
      }), node.parameters.map(function (parameter) {
        return parameter.visit(_this);
      }), node.isCast, node.shaderType);
      result.protocolDecl = node.protocolDecl;
      result.possibleOverloads = node.possibleOverloads;
      return result;
    }
  }, {
    key: "visitNativeTypeInstance",
    value: function visitNativeTypeInstance(node) {
      var _this2 = this;
      return new NativeTypeInstance(node.type.visit(this), node.typeArguments.map(function (argument) {
        return argument.visit(_this2);
      }));
    }
  }, {
    key: "visitFuncParameter",
    value: function visitFuncParameter(node) {
      var result = new FuncParameter(node.origin, node.name, node.type.visit(this));
      this._mapNode(node, result);
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitVariableDecl",
    value: function visitVariableDecl(node) {
      var result = new VariableDecl(node.origin, node.name, node.type.visit(this), Node.visit(node.initializer, this));
      this._mapNode(node, result);
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitBlock",
    value: function visitBlock(node) {
      var result = new Block(node.origin);
      var _iterator = _createForOfIteratorHelper(node.statements),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var statement = _step.value;
          result.add(statement.visit(this));
        }
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
      return result;
    }
  }, {
    key: "visitCommaExpression",
    value: function visitCommaExpression(node) {
      var _this3 = this;
      return new CommaExpression(node.origin, node.list.map(function (expression) {
        var result = expression.visit(_this3);
        if (!result) throw new Error("Null result from " + expression);
        return result;
      }));
    }
  }, {
    key: "visitProtocolRef",
    value: function visitProtocolRef(node) {
      return node;
    }
  }, {
    key: "visitTypeRef",
    value: function visitTypeRef(node) {
      var _this4 = this;
      var result = new TypeRef(node.origin, node.name, node.typeArguments.map(function (typeArgument) {
        return typeArgument.visit(_this4);
      }));
      result.type = Node.visit(node.type, this);
      return result;
    }
  }, {
    key: "visitField",
    value: function visitField(node) {
      return new Field(node.origin, node.name, node.type.visit(this));
    }
  }, {
    key: "visitEnumMember",
    value: function visitEnumMember(node) {
      return new EnumMember(node.origin, node.name, node.value.visit(this));
    }
  }, {
    key: "visitEnumLiteral",
    value: function visitEnumLiteral(node) {
      var result = new EnumLiteral(node.origin, node.member);
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitReferenceType",
    value: function visitReferenceType(node) {
      return new node.constructor(node.origin, node.addressSpace, node.elementType.visit(this));
    }
  }, {
    key: "visitPtrType",
    value: function visitPtrType(node) {
      return this.visitReferenceType(node);
    }
  }, {
    key: "visitArrayRefType",
    value: function visitArrayRefType(node) {
      return this.visitReferenceType(node);
    }
  }, {
    key: "visitArrayType",
    value: function visitArrayType(node) {
      return new ArrayType(node.origin, node.elementType.visit(this), node.numElements.visit(this));
    }
  }, {
    key: "visitAssignment",
    value: function visitAssignment(node) {
      var result = new Assignment(node.origin, node.lhs.visit(this), node.rhs.visit(this));
      result.type = Node.visit(node.type, this);
      return result;
    }
  }, {
    key: "visitReadModifyWriteExpression",
    value: function visitReadModifyWriteExpression(node) {
      var result = new ReadModifyWriteExpression(node.origin, node.lValue.visit(this));
      result.oldValueVar = node.oldValueVar.visit(this);
      result.newValueVar = node.newValueVar.visit(this);
      result.newValueExp = node.newValueExp.visit(this);
      result.resultExp = node.resultExp.visit(this);
      return result;
    }
  }, {
    key: "visitDereferenceExpression",
    value: function visitDereferenceExpression(node) {
      var result = new DereferenceExpression(node.origin, node.ptr.visit(this));
      result.type = Node.visit(node.type, this);
      result.addressSpace = node.addressSpace;
      return result;
    }
  }, {
    key: "_handlePropertyAccessExpression",
    value: function _handlePropertyAccessExpression(result, node) {
      result.possibleGetOverloads = node.possibleGetOverloads;
      result.possibleSetOverloads = node.possibleSetOverloads;
      result.possibleAndOverloads = node.possibleAndOverloads;
      result.baseType = Node.visit(node.baseType, this);
      result.callForGet = Node.visit(node.callForGet, this);
      result.resultTypeForGet = Node.visit(node.resultTypeForGet, this);
      result.callForAnd = Node.visit(node.callForAnd, this);
      result.resultTypeForAnd = Node.visit(node.resultTypeForAnd, this);
      result.callForSet = Node.visit(node.callForSet, this);
      result.errorForSet = node.errorForSet;
      result.updateCalls();
    }
  }, {
    key: "visitDotExpression",
    value: function visitDotExpression(node) {
      var result = new DotExpression(node.origin, node.struct.visit(this), node.fieldName);
      this._handlePropertyAccessExpression(result, node);
      return result;
    }
  }, {
    key: "visitIndexExpression",
    value: function visitIndexExpression(node) {
      var result = new IndexExpression(node.origin, node.array.visit(this), node.index.visit(this));
      this._handlePropertyAccessExpression(result, node);
      return result;
    }
  }, {
    key: "visitMakePtrExpression",
    value: function visitMakePtrExpression(node) {
      var result = new MakePtrExpression(node.origin, node.lValue.visit(this));
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitMakeArrayRefExpression",
    value: function visitMakeArrayRefExpression(node) {
      var result = new MakeArrayRefExpression(node.origin, node.lValue.visit(this));
      if (node.numElements) result.numElements = node.numElements.visit(this);
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitConvertPtrToArrayRefExpression",
    value: function visitConvertPtrToArrayRefExpression(node) {
      var result = new ConvertPtrToArrayRefExpression(node.origin, node.lValue.visit(this));
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitVariableRef",
    value: function visitVariableRef(node) {
      var result = new VariableRef(node.origin, node.name);
      result.variable = this._getMapping(node.variable);
      return result;
    }
  }, {
    key: "visitReturn",
    value: function visitReturn(node) {
      return new Return(node.origin, Node.visit(node.value, this));
    }
  }, {
    key: "visitContinue",
    value: function visitContinue(node) {
      return new Continue(node.origin);
    }
  }, {
    key: "visitBreak",
    value: function visitBreak(node) {
      return new Break(node.origin);
    }
  }, {
    key: "visitTrapStatement",
    value: function visitTrapStatement(node) {
      return new TrapStatement(node.origin);
    }
  }, {
    key: "visitGenericLiteral",
    value: function visitGenericLiteral(node) {
      // FIXME: This doesn't seem right.
      var result = new IntLiteral(node.origin, node.value);
      result.type = node.type.visit(this);
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitGenericLiteralType",
    value: function visitGenericLiteralType(node) {
      var result = new node.constructor(node.origin, node.value);
      result.type = Node.visit(node.type, this);
      result.preferredType = node.preferredType.visit(this);
      return result;
    }
  }, {
    key: "visitBoolLiteral",
    value: function visitBoolLiteral(node) {
      return node;
    }
  }, {
    key: "visitNullLiteral",
    value: function visitNullLiteral(node) {
      var result = new NullLiteral(node.origin);
      result.type = node.type.visit(this);
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitNullType",
    value: function visitNullType(node) {
      var result = new NullType(node.origin);
      result.type = Node.visit(node.type, this);
      return result;
    }
  }, {
    key: "processDerivedCallData",
    value: function processDerivedCallData(node, result) {
      var _this5 = this;
      var handleTypeArguments = function handleTypeArguments(actualTypeArguments) {
        if (actualTypeArguments) return actualTypeArguments.map(function (actualTypeArgument) {
          return actualTypeArgument.visit(_this5);
        });else return null;
      };
      result.actualTypeArguments = handleTypeArguments(node.actualTypeArguments);
      result.instantiatedActualTypeArguments = handleTypeArguments(node.instantiatedActualTypeArguments);
      var argumentTypes = node.argumentTypes;
      if (argumentTypes) result.argumentTypes = argumentTypes.map(function (argumentType) {
        return argumentType.visit(_this5);
      });
      result.func = node.func;
      result.nativeFuncInstance = node.nativeFuncInstance;
      result.possibleOverloads = node.possibleOverloads;
      if (node.isCast) result.setCastData(node.returnType.visit(this));
      result.resultType = Node.visit(node.resultType, this);
      result.resultEPtr = node.resultEPtr;
      return result;
    }
  }, {
    key: "visitCallExpression",
    value: function visitCallExpression(node) {
      var _this6 = this;
      var result = new CallExpression(node.origin, node.name, node.typeArguments.map(function (typeArgument) {
        return typeArgument.visit(_this6);
      }), node.argumentList.map(function (argument) {
        return Node.visit(argument, _this6);
      }));
      return this.processDerivedCallData(node, result);
    }
  }, {
    key: "visitFunctionLikeBlock",
    value: function visitFunctionLikeBlock(node) {
      var _this7 = this;
      var result = new FunctionLikeBlock(node.origin, Node.visit(node.returnType, this), node.argumentList.map(function (argument) {
        return argument.visit(_this7);
      }), node.parameters.map(function (parameter) {
        return parameter.visit(_this7);
      }), node.body.visit(this));
      result.returnEPtr = node.returnEPtr;
      return result;
    }
  }, {
    key: "visitLogicalNot",
    value: function visitLogicalNot(node) {
      var result = new LogicalNot(node.origin, node.operand.visit(this));
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitLogicalExpression",
    value: function visitLogicalExpression(node) {
      var result = new LogicalExpression(node.origin, node.text, node.left.visit(this), node.right.visit(this));
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitIfStatement",
    value: function visitIfStatement(node) {
      return new IfStatement(node.origin, node.conditional.visit(this), node.body.visit(this), Node.visit(node.elseBody, this));
    }
  }, {
    key: "visitWhileLoop",
    value: function visitWhileLoop(node) {
      return new WhileLoop(node.origin, node.conditional.visit(this), node.body.visit(this));
    }
  }, {
    key: "visitDoWhileLoop",
    value: function visitDoWhileLoop(node) {
      return new DoWhileLoop(node.origin, node.body.visit(this), node.conditional.visit(this));
    }
  }, {
    key: "visitForLoop",
    value: function visitForLoop(node) {
      return new ForLoop(node.origin, Node.visit(node.initialization, this), Node.visit(node.condition, this), Node.visit(node.increment, this), node.body.visit(this));
    }
  }, {
    key: "visitSwitchStatement",
    value: function visitSwitchStatement(node) {
      var result = new SwitchStatement(node.origin, Node.visit(node.value, this));
      var _iterator2 = _createForOfIteratorHelper(node.switchCases),
        _step2;
      try {
        for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
          var switchCase = _step2.value;
          result.add(switchCase.visit(this));
        }
      } catch (err) {
        _iterator2.e(err);
      } finally {
        _iterator2.f();
      }
      result.type = Node.visit(node.type, this);
      return result;
    }
  }, {
    key: "visitSwitchCase",
    value: function visitSwitchCase(node) {
      return new SwitchCase(node.origin, Node.visit(node.value, this), node.body.visit(this));
    }
  }, {
    key: "visitAnonymousVariable",
    value: function visitAnonymousVariable(node) {
      var result = new AnonymousVariable(node.origin, node.type.visit(this));
      result._index = node._index;
      this._mapNode(node, result);
      result.ePtr = node.ePtr;
      return result;
    }
  }, {
    key: "visitIdentityExpression",
    value: function visitIdentityExpression(node) {
      return new IdentityExpression(node.target.visit(this));
    }
  }]);
}();