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
function _callSuper(t, o, e) { return o = _getPrototypeOf(o), _possibleConstructorReturn(t, _isNativeReflectConstruct() ? Reflect.construct(o, e || [], _getPrototypeOf(t).constructor) : o.apply(t, e)); }
function _possibleConstructorReturn(t, e) { if (e && ("object" == _typeof(e) || "function" == typeof e)) return e; if (void 0 !== e) throw new TypeError("Derived constructors may only return object or undefined"); return _assertThisInitialized(t); }
function _assertThisInitialized(e) { if (void 0 === e) throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); return e; }
function _isNativeReflectConstruct() { try { var t = !Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], function () {})); } catch (t) {} return (_isNativeReflectConstruct = function _isNativeReflectConstruct() { return !!t; })(); }
function _getPrototypeOf(t) { return _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function (t) { return t.__proto__ || Object.getPrototypeOf(t); }, _getPrototypeOf(t); }
function _inherits(t, e) { if ("function" != typeof e && null !== e) throw new TypeError("Super expression must either be null or a function"); t.prototype = Object.create(e && e.prototype, { constructor: { value: t, writable: !0, configurable: !0 } }), Object.defineProperty(t, "prototype", { writable: !1 }), e && _setPrototypeOf(t, e); }
function _setPrototypeOf(t, e) { return _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function (t, e) { return t.__proto__ = e, t; }, _setPrototypeOf(t, e); }
var StatementCloner = /*#__PURE__*/function (_Rewriter) {
  function StatementCloner() {
    _classCallCheck(this, StatementCloner);
    return _callSuper(this, StatementCloner, arguments);
  }
  _inherits(StatementCloner, _Rewriter);
  return _createClass(StatementCloner, [{
    key: "visitFuncDef",
    value: function visitFuncDef(node) {
      var _this = this;
      var typeParameters = node.typeParameters.map(function (typeParameter) {
        return typeParameter.visit(_this);
      });
      var result = new FuncDef(node.origin, node.name, node.returnType.visit(this), typeParameters, node.parameters.map(function (parameter) {
        return parameter.visit(_this);
      }), node.body.visit(this), node.isCast, node.shaderType);
      result.isRestricted = node.isRestricted;
      return result;
    }
  }, {
    key: "visitNativeFunc",
    value: function visitNativeFunc(node) {
      var _this2 = this;
      var result = new NativeFunc(node.origin, node.name, node.returnType.visit(this), node.typeParameters.map(function (typeParameter) {
        return typeParameter.visit(_this2);
      }), node.parameters.map(function (parameter) {
        return parameter.visit(_this2);
      }), node.isCast, node.shaderType);
      result.isRestricted = node.isRestricted;
      return result;
    }
  }, {
    key: "visitNativeType",
    value: function visitNativeType(node) {
      var _this3 = this;
      return new NativeType(node.origin, node.name, node.typeParameters.map(function (typeParameter) {
        return typeParameter.visit(_this3);
      }));
    }
  }, {
    key: "visitTypeDef",
    value: function visitTypeDef(node) {
      var _this4 = this;
      return new TypeDef(node.origin, node.name, node.typeParameters.map(function (typeParameter) {
        return typeParameter.visit(_this4);
      }), node.type.visit(this));
    }
  }, {
    key: "visitStructType",
    value: function visitStructType(node) {
      var _this5 = this;
      var result = new StructType(node.origin, node.name, node.typeParameters.map(function (typeParameter) {
        return typeParameter.visit(_this5);
      }));
      var _iterator = _createForOfIteratorHelper(node.fields),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var field = _step.value;
          result.add(field.visit(this));
        }
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
      return result;
    }
  }, {
    key: "visitConstexprTypeParameter",
    value: function visitConstexprTypeParameter(node) {
      return new ConstexprTypeParameter(node.origin, node.name, node.type.visit(this));
    }
  }, {
    key: "visitProtocolDecl",
    value: function visitProtocolDecl(node) {
      var result = new ProtocolDecl(node.origin, node.name);
      var _iterator2 = _createForOfIteratorHelper(node.extends),
        _step2;
      try {
        for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
          var protocol = _step2.value;
          result.addExtends(protocol.visit(this));
        }
      } catch (err) {
        _iterator2.e(err);
      } finally {
        _iterator2.f();
      }
      var _iterator3 = _createForOfIteratorHelper(node.signatures),
        _step3;
      try {
        for (_iterator3.s(); !(_step3 = _iterator3.n()).done;) {
          var signature = _step3.value;
          result.add(signature.visit(this));
        }
      } catch (err) {
        _iterator3.e(err);
      } finally {
        _iterator3.f();
      }
      return result;
    }
  }, {
    key: "visitTypeVariable",
    value: function visitTypeVariable(node) {
      return new TypeVariable(node.origin, node.name, Node.visit(node.protocol, this));
    }
  }, {
    key: "visitProtocolRef",
    value: function visitProtocolRef(node) {
      return new ProtocolRef(node.origin, node.name);
    }
  }, {
    key: "visitBoolLiteral",
    value: function visitBoolLiteral(node) {
      return new BoolLiteral(node.origin, node.value);
    }
  }, {
    key: "visitTypeOrVariableRef",
    value: function visitTypeOrVariableRef(node) {
      return new TypeOrVariableRef(node.origin, node.name);
    }
  }, {
    key: "visitEnumType",
    value: function visitEnumType(node) {
      var result = new EnumType(node.origin, node.name, node.baseType.visit(this));
      var _iterator4 = _createForOfIteratorHelper(node.members),
        _step4;
      try {
        for (_iterator4.s(); !(_step4 = _iterator4.n()).done;) {
          var member = _step4.value;
          result.add(member);
        }
      } catch (err) {
        _iterator4.e(err);
      } finally {
        _iterator4.f();
      }
      return result;
    }
  }]);
}(Rewriter);