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
function _getPrototypeOf(t) { return _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function (t) { return t.__proto__ || Object.getPrototypeOf(t); }, _getPrototypeOf(t); }
function _inherits(t, e) { if ("function" != typeof e && null !== e) throw new TypeError("Super expression must either be null or a function"); t.prototype = Object.create(e && e.prototype, { constructor: { value: t, writable: !0, configurable: !0 } }), Object.defineProperty(t, "prototype", { writable: !1 }), e && _setPrototypeOf(t, e); }
function _setPrototypeOf(t, e) { return _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function (t, e) { return t.__proto__ = e, t; }, _setPrototypeOf(t, e); }
var PropertyAccessExpression = /*#__PURE__*/function (_Expression) {
  function PropertyAccessExpression(origin, base) {
    var _this;
    _classCallCheck(this, PropertyAccessExpression);
    _this = _callSuper(this, PropertyAccessExpression, [origin]);
    _this.base = base;
    _this._isLValue = null; // We use null to indicate that we don't know yet.
    _this.addressSpace = null;
    _this._notLValueReason = null;
    return _this;
  }
  _inherits(PropertyAccessExpression, _Expression);
  return _createClass(PropertyAccessExpression, [{
    key: "resultType",
    get: function get() {
      return this.resultTypeForGet ? this.resultTypeForGet : this.resultTypeForAnd;
    }
  }, {
    key: "isLValue",
    get: function get() {
      return this._isLValue;
    },
    set: function set(value) {
      this._isLValue = value;
    }
  }, {
    key: "notLValueReason",
    get: function get() {
      return this._notLValueReason;
    },
    set: function set(value) {
      this._notLValueReason = value;
    }
  }, {
    key: "rewriteAfterCloning",
    value: function rewriteAfterCloning() {
      // At this point, node.base.isLValue will only return true if it's possible to get a pointer to it,
      // since we will no longer see any DotExpressions or IndexExpressions. Also, node is a newly created
      // node and everything beneath it is newly created, so we can edit it in-place.

      if ((this.base.isLValue || this.baseType.isRef) && this.callForAnd) return new DereferenceExpression(this.origin, this.callForAnd, this.resultType, this.callForAnd.resultType.addressSpace);
      if (this.callForGet) return this.callForGet;
      if (!this.callForAnd) throw new Error(this.origin.originString + ": Property access without getter and ander: " + this);
      var anonVar = new AnonymousVariable(this.origin, this.baseType);
      this.callForAnd.argumentList[0] = this.baseType.unifyNode.argumentForAndOverload(this.origin, VariableRef.wrap(anonVar));
      return new CommaExpression(this.origin, [anonVar, new Assignment(this.origin, VariableRef.wrap(anonVar), this.base, this.baseType), new DereferenceExpression(this.origin, this.callForAnd, this.resultType, this.callForAnd.resultType.addressSpace)]);
    }
  }, {
    key: "updateCalls",
    value: function updateCalls() {
      if (this.callForGet) this.callForGet.argumentList[0] = this.base;
      if (this.callForAnd) this.callForAnd.argumentList[0] = this.baseType.argumentForAndOverload(this.origin, this.base);
      if (this.callForSet) this.callForSet.argumentList[0] = this.base;
    }
  }, {
    key: "emitGet",
    value: function emitGet(base) {
      var result = this.visit(new Rewriter());
      result.base = base;
      result.updateCalls();
      return result.rewriteAfterCloning();
    }
  }, {
    key: "emitSet",
    value: function emitSet(base, value) {
      var result = this.visit(new Rewriter());
      if (!result.callForSet) throw new WTypeError(this.origin.originString, "Cannot emit set because: " + this.errorForSet.typeErrorMessage);
      result.base = base;
      result.updateCalls();
      result.callForSet.argumentList[result.callForSet.argumentList.length - 1] = value;
      return result.callForSet;
    }
  }]);
}(Expression);