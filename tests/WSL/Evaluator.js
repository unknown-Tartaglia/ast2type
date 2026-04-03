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

// This is a combined LHS/RHS evaluator that passes around EPtr's to everything.
function _typeof(o) { "@babel/helpers - typeof"; return _typeof = "function" == typeof Symbol && "symbol" == typeof Symbol.iterator ? function (o) { return typeof o; } : function (o) { return o && "function" == typeof Symbol && o.constructor === Symbol && o !== Symbol.prototype ? "symbol" : typeof o; }, _typeof(o); }
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
var Evaluator = /*#__PURE__*/function (_Visitor) {
  function Evaluator(program) {
    var _this;
    _classCallCheck(this, Evaluator);
    _this = _callSuper(this, Evaluator);
    _this._program = program;
    return _this;
  }

  // You must snapshot if you use a value in rvalue context. For example, a call expression will
  // snapshot all of its arguments immedaitely upon executing them. In general, it should not be
  // possible for a pointer returned from a visit method in rvalue context to live across any effects.
  _inherits(Evaluator, _Visitor);
  return _createClass(Evaluator, [{
    key: "_snapshot",
    value: function _snapshot(type, dstPtr, srcPtr) {
      var size = type.size;
      if (size == null) throw new Error("Cannot get size of type: " + type + " (size = " + size + ", constructor = " + type.constructor.name + ")");
      if (!dstPtr) dstPtr = new EPtr(new EBuffer(size), 0);
      dstPtr.copyFrom(srcPtr, size);
      return dstPtr;
    }
  }, {
    key: "runFunc",
    value: function runFunc(func) {
      var _this2 = this;
      return EBuffer.disallowAllocation(function () {
        return _this2._runBody(func.returnType, func.returnEPtr, func.body);
      });
    }
  }, {
    key: "_runBody",
    value: function _runBody(type, ptr, block) {
      if (!ptr) throw new Error("Null ptr");
      try {
        block.visit(this);
        // FIXME: We should have a check that there is no way to drop out of a function without
        // returning unless the function returns void.
        return null;
      } catch (e) {
        if (e == BreakException || e == ContinueException) throw new Error("Should not see break/continue at function scope");
        if (e instanceof ReturnException) {
          var result = this._snapshot(type, ptr, e.value);
          return result;
        }
        throw e;
      }
    }
  }, {
    key: "visitFunctionLikeBlock",
    value: function visitFunctionLikeBlock(node) {
      for (var i = 0; i < node.argumentList.length; ++i) {
        node.parameters[i].ePtr.copyFrom(node.argumentList[i].visit(this), node.parameters[i].type.size);
      }
      var result = this._runBody(node.returnType, node.returnEPtr, node.body);
      return result;
    }
  }, {
    key: "visitReturn",
    value: function visitReturn(node) {
      throw new ReturnException(node.value ? node.value.visit(this) : null);
    }
  }, {
    key: "visitVariableDecl",
    value: function visitVariableDecl(node) {
      if (!node.ePtr.buffer) throw new Error("eptr without buffer in " + node);
      node.type.populateDefaultValue(node.ePtr.buffer, node.ePtr.offset);
      if (node.initializer) node.ePtr.copyFrom(node.initializer.visit(this), node.type.size);
    }
  }, {
    key: "visitAssignment",
    value: function visitAssignment(node) {
      var target = node.lhs.visit(this);
      var source = node.rhs.visit(this);
      target.copyFrom(source, node.type.size);
      return target;
    }
  }, {
    key: "visitIdentityExpression",
    value: function visitIdentityExpression(node) {
      return node.target.visit(this);
    }
  }, {
    key: "visitDereferenceExpression",
    value: function visitDereferenceExpression(node) {
      var ptr = node.ptr.visit(this).loadValue();
      if (!ptr) throw new WTrapError(node.origin.originString, "Null dereference");
      return ptr;
    }
  }, {
    key: "visitMakePtrExpression",
    value: function visitMakePtrExpression(node) {
      var ptr = node.lValue.visit(this);
      return node.ePtr.box(ptr);
    }
  }, {
    key: "visitMakeArrayRefExpression",
    value: function visitMakeArrayRefExpression(node) {
      return node.ePtr.box(new EArrayRef(node.lValue.visit(this), node.numElements.visit(this).loadValue()));
    }
  }, {
    key: "visitConvertPtrToArrayRefExpression",
    value: function visitConvertPtrToArrayRefExpression(node) {
      return node.ePtr.box(new EArrayRef(node.lValue.visit(this).loadValue(), 1));
    }
  }, {
    key: "visitCommaExpression",
    value: function visitCommaExpression(node) {
      var result;
      var _iterator = _createForOfIteratorHelper(node.list),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var expression = _step.value;
          result = expression.visit(this);
        }
        // This should almost snapshot, except that tail-returning a pointer is totally OK.
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
      return result;
    }
  }, {
    key: "visitVariableRef",
    value: function visitVariableRef(node) {
      return node.variable.ePtr;
    }
  }, {
    key: "visitGenericLiteral",
    value: function visitGenericLiteral(node) {
      return node.ePtr.box(node.valueForSelectedType);
    }
  }, {
    key: "visitNullLiteral",
    value: function visitNullLiteral(node) {
      return node.ePtr.box(null);
    }
  }, {
    key: "visitBoolLiteral",
    value: function visitBoolLiteral(node) {
      return node.ePtr.box(node.value);
    }
  }, {
    key: "visitEnumLiteral",
    value: function visitEnumLiteral(node) {
      return node.ePtr.box(node.member.value.unifyNode.valueForSelectedType);
    }
  }, {
    key: "visitLogicalNot",
    value: function visitLogicalNot(node) {
      var result = !node.operand.visit(this).loadValue();
      return node.ePtr.box(result);
    }
  }, {
    key: "visitLogicalExpression",
    value: function visitLogicalExpression(node) {
      var lhs = node.left.visit(this).loadValue();
      var rhs = node.right.visit(this).loadValue();
      var result;
      switch (node.text) {
        case "&&":
          result = lhs && rhs;
          break;
        case "||":
          result = lhs || rhs;
          break;
        default:
          throw new Error("Unknown type of logical expression");
      }
      return node.ePtr.box(result);
    }
  }, {
    key: "visitIfStatement",
    value: function visitIfStatement(node) {
      if (node.conditional.visit(this).loadValue()) return node.body.visit(this);else if (node.elseBody) return node.elseBody.visit(this);
    }
  }, {
    key: "visitWhileLoop",
    value: function visitWhileLoop(node) {
      while (node.conditional.visit(this).loadValue()) {
        try {
          node.body.visit(this);
        } catch (e) {
          if (e == BreakException) break;
          if (e == ContinueException) continue;
          throw e;
        }
      }
    }
  }, {
    key: "visitDoWhileLoop",
    value: function visitDoWhileLoop(node) {
      do {
        try {
          node.body.visit(this);
        } catch (e) {
          if (e == BreakException) break;
          if (e == ContinueException) continue;
          throw e;
        }
      } while (node.conditional.visit(this).loadValue());
    }
  }, {
    key: "visitForLoop",
    value: function visitForLoop(node) {
      for (node.initialization ? node.initialization.visit(this) : true; node.condition ? node.condition.visit(this).loadValue() : true; node.increment ? node.increment.visit(this) : true) {
        try {
          node.body.visit(this);
        } catch (e) {
          if (e == BreakException) break;
          if (e == ContinueException) continue;
          throw e;
        }
      }
    }
  }, {
    key: "visitSwitchStatement",
    value: function visitSwitchStatement(node) {
      var _this3 = this;
      var findAndRunCast = function findAndRunCast(predicate) {
        for (var i = 0; i < node.switchCases.length; ++i) {
          var switchCase = node.switchCases[i];
          if (predicate(switchCase)) {
            try {
              for (var j = i; j < node.switchCases.length; ++j) node.switchCases[j].visit(_this3);
            } catch (e) {
              if (e != BreakException) throw e;
            }
            return true;
          }
        }
        return false;
      };
      var value = node.value.visit(this).loadValue();
      var found = findAndRunCast(function (switchCase) {
        if (switchCase.isDefault) return false;
        return node.type.unifyNode.valuesEqual(value, switchCase.value.unifyNode.valueForSelectedType);
      });
      if (found) return;
      found = findAndRunCast(function (switchCase) {
        return switchCase.isDefault;
      });
      if (!found) throw new Error("Switch statement did not find case");
    }
  }, {
    key: "visitBreak",
    value: function visitBreak(node) {
      throw BreakException;
    }
  }, {
    key: "visitContinue",
    value: function visitContinue(node) {
      throw ContinueException;
    }
  }, {
    key: "visitTrapStatement",
    value: function visitTrapStatement(node) {
      throw new WTrapError(node.origin.originString, "Trap statement");
    }
  }, {
    key: "visitAnonymousVariable",
    value: function visitAnonymousVariable(node) {
      node.type.populateDefaultValue(node.ePtr.buffer, node.ePtr.offset);
    }
  }, {
    key: "visitCallExpression",
    value: function visitCallExpression(node) {
      var _this4 = this;
      // We evaluate inlined ASTs, so this can only be a native call.
      var callArguments = [];
      var _loop = function _loop() {
        var argument = node.argumentList[i];
        var type = node.nativeFuncInstance.parameterTypes[i];
        if (!type || !argument) throw new Error("Cannot get type or argument; i = " + i + ", argument = " + argument + ", type = " + type + "; in " + node);
        var argumentValue = argument.visit(_this4);
        if (!argumentValue) throw new Error("Null argument value, i = " + i + ", node = " + node);
        callArguments.push(function () {
          var result = _this4._snapshot(type, null, argumentValue);
          return result;
        });
      };
      for (var i = 0; i < node.argumentList.length; ++i) {
        _loop();
      }

      // For simplicity, we allow intrinsics to just allocate new buffers, and we allocate new
      // buffers when snapshotting their arguments. This is not observable to the user, so it's OK.
      var result = EBuffer.allowAllocation(function () {
        return node.func.implementation(callArguments.map(function (thunk) {
          return thunk();
        }), node);
      });
      result = this._snapshot(node.nativeFuncInstance.returnType, node.resultEPtr, result);
      return result;
    }
  }]);
}(Visitor);