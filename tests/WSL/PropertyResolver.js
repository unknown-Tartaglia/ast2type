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
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
function _callSuper(t, o, e) { return o = _getPrototypeOf(o), _possibleConstructorReturn(t, _isNativeReflectConstruct() ? Reflect.construct(o, e || [], _getPrototypeOf(t).constructor) : o.apply(t, e)); }
function _possibleConstructorReturn(t, e) { if (e && ("object" == _typeof(e) || "function" == typeof e)) return e; if (void 0 !== e) throw new TypeError("Derived constructors may only return object or undefined"); return _assertThisInitialized(t); }
function _assertThisInitialized(e) { if (void 0 === e) throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); return e; }
function _isNativeReflectConstruct() { try { var t = !Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], function () {})); } catch (t) {} return (_isNativeReflectConstruct = function _isNativeReflectConstruct() { return !!t; })(); }
function _superPropGet(t, o, e, r) { var p = _get(_getPrototypeOf(1 & r ? t.prototype : t), o, e); return 2 & r && "function" == typeof p ? function (t) { return p.apply(e, t); } : p; }
function _get() { return _get = "undefined" != typeof Reflect && Reflect.get ? Reflect.get.bind() : function (e, t, r) { var p = _superPropBase(e, t); if (p) { var n = Object.getOwnPropertyDescriptor(p, t); return n.get ? n.get.call(arguments.length < 3 ? e : r) : n.value; } }, _get.apply(null, arguments); }
function _superPropBase(t, o) { for (; !{}.hasOwnProperty.call(t, o) && null !== (t = _getPrototypeOf(t));); return t; }
function _getPrototypeOf(t) { return _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function (t) { return t.__proto__ || Object.getPrototypeOf(t); }, _getPrototypeOf(t); }
function _inherits(t, e) { if ("function" != typeof e && null !== e) throw new TypeError("Super expression must either be null or a function"); t.prototype = Object.create(e && e.prototype, { constructor: { value: t, writable: !0, configurable: !0 } }), Object.defineProperty(t, "prototype", { writable: !1 }), e && _setPrototypeOf(t, e); }
function _setPrototypeOf(t, e) { return _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function (t, e) { return t.__proto__ = e, t; }, _setPrototypeOf(t, e); }
var PropertyResolver = /*#__PURE__*/function (_Visitor) {
  function PropertyResolver() {
    _classCallCheck(this, PropertyResolver);
    return _callSuper(this, PropertyResolver, arguments);
  }
  _inherits(PropertyResolver, _Visitor);
  return _createClass(PropertyResolver, [{
    key: "_visitRValuesWithinLValue",
    value: function _visitRValuesWithinLValue(node) {
      var _this = this;
      var visit = function visit(node) {
        return node.visit(_this);
      };
      var RValueFinder = /*#__PURE__*/function () {
        function RValueFinder() {
          _classCallCheck(this, RValueFinder);
        }
        return _createClass(RValueFinder, [{
          key: "visitDotExpression",
          value: function visitDotExpression(node) {
            node.struct.visit(this);
          }
        }, {
          key: "visitIndexExpression",
          value: function visitIndexExpression(node) {
            node.array.visit(this);
            visit(node.index);
          }
        }, {
          key: "visitVariableRef",
          value: function visitVariableRef(node) {}
        }, {
          key: "visitDereferenceExpression",
          value: function visitDereferenceExpression(node) {
            visit(node.ptr);
          }
        }, {
          key: "visitIdentityExpression",
          value: function visitIdentityExpression(node) {
            node.target.visit(this);
          }
        }, {
          key: "visitMakeArrayRefExpression",
          value: function visitMakeArrayRefExpression(node) {
            visit(node.lValue);
          }
        }]);
      }();
      node.visit(new RValueFinder());
    }
  }, {
    key: "_visitPropertyAccess",
    value: function _visitPropertyAccess(node) {
      var newNode = node.visit(new NormalUsePropertyResolver());
      newNode.visit(this);
      node.become(newNode);
    }
  }, {
    key: "visitDotExpression",
    value: function visitDotExpression(node) {
      this._visitPropertyAccess(node);
    }
  }, {
    key: "visitIndexExpression",
    value: function visitIndexExpression(node) {
      this._visitPropertyAccess(node);
    }
  }, {
    key: "_handleReadModifyWrite",
    value: function _handleReadModifyWrite(node) {
      var type = node.oldValueVar.type;
      if (!type) throw new Error("Null type");
      var simpleLHS = node.lValue.visit(new NormalUsePropertyResolver());
      if (simpleLHS.isLValue) {
        if (!simpleLHS.addressSpace) throw new Error(node.origin.originString + ": LHS without address space: " + simpleLHS);
        var ptrType = new PtrType(node.origin, simpleLHS.addressSpace, type);
        var ptrVar = new AnonymousVariable(node.origin, ptrType);
        node.become(new CommaExpression(node.origin, [node.oldValueVar, node.newValueVar, ptrVar, new Assignment(node.origin, VariableRef.wrap(ptrVar), new MakePtrExpression(node.origin, simpleLHS), ptrType), new Assignment(node.origin, node.oldValueRef(), new DereferenceExpression(node.origin, VariableRef.wrap(ptrVar), type, simpleLHS.addressSpace), type), new Assignment(node.origin, node.newValueRef(), node.newValueExp, type), new Assignment(node.origin, new DereferenceExpression(node.origin, VariableRef.wrap(ptrVar), type, simpleLHS.addressSpace), node.newValueRef(), type), node.resultExp]));
        return;
      }
      var result = new ReadModifyWriteExpression(node.origin, node.lValue.base, node.lValue.baseType);
      result.newValueExp = new CommaExpression(node.origin, [node.oldValueVar, node.newValueVar, new Assignment(node.origin, node.oldValueRef(), node.lValue.emitGet(result.oldValueRef()), type), new Assignment(node.origin, node.newValueRef(), node.newValueExp, type), node.lValue.emitSet(result.oldValueRef(), node.newValueRef())]);
      result.resultExp = node.newValueRef();
      this._handleReadModifyWrite(result);
      node.become(result);
    }
  }, {
    key: "visitReadModifyWriteExpression",
    value: function visitReadModifyWriteExpression(node) {
      node.newValueExp.visit(this);
      node.resultExp.visit(this);
      this._visitRValuesWithinLValue(node.lValue);
      this._handleReadModifyWrite(node);
    }
  }, {
    key: "visitAssignment",
    value: function visitAssignment(node) {
      this._visitRValuesWithinLValue(node.lhs);
      node.rhs.visit(this);
      var simpleLHS = node.lhs.visit(new NormalUsePropertyResolver());
      if (simpleLHS.isLValue) {
        node.lhs.become(simpleLHS);
        return;
      }
      if (!(node.lhs instanceof PropertyAccessExpression)) throw new Error("Unexpected lhs type: " + node.lhs.constructor.name);
      var result = new ReadModifyWriteExpression(node.origin, node.lhs.base, node.lhs.baseType);
      var resultVar = new AnonymousVariable(node.origin, node.type);
      result.newValueExp = new CommaExpression(node.origin, [resultVar, new Assignment(node.origin, VariableRef.wrap(resultVar), node.rhs, node.type), node.lhs.emitSet(result.oldValueRef(), VariableRef.wrap(resultVar))]);
      result.resultExp = VariableRef.wrap(resultVar);
      this._handleReadModifyWrite(result);
      node.become(result);
    }
  }, {
    key: "visitMakePtrExpression",
    value: function visitMakePtrExpression(node) {
      _superPropGet(PropertyResolver, "visitMakePtrExpression", this, 3)([node]);
      if (!node.lValue.isLValue) throw new WTypeError(node.origin.originString, "Not an lvalue: " + node.lValue);
    }
  }, {
    key: "visitMakeArrayRefExpression",
    value: function visitMakeArrayRefExpression(node) {
      _superPropGet(PropertyResolver, "visitMakeArrayRefExpression", this, 3)([node]);
      if (!node.lValue.isLValue) throw new WTypeError(node.origin.originString, "Not an lvalue: " + node.lValue);
    }
  }]);
}(Visitor);