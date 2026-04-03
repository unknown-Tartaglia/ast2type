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
var CallExpression = /*#__PURE__*/function (_Expression) {
  function CallExpression(origin, name, typeArguments, argumentList) {
    var _this;
    _classCallCheck(this, CallExpression);
    _this = _callSuper(this, CallExpression, [origin]);
    _this._name = name;
    _this._typeArguments = typeArguments;
    _this._argumentList = argumentList;
    _this.func = null;
    _this._isCast = false;
    _this._returnType = null;
    return _this;
  }
  _inherits(CallExpression, _Expression);
  return _createClass(CallExpression, [{
    key: "name",
    get: function get() {
      return this._name;
    }
  }, {
    key: "typeArguments",
    get: function get() {
      return this._typeArguments;
    }
  }, {
    key: "argumentList",
    get: function get() {
      return this._argumentList;
    }
  }, {
    key: "isCast",
    get: function get() {
      return this._isCast;
    }
  }, {
    key: "returnType",
    get: function get() {
      return this._returnType;
    }
  }, {
    key: "resolve",
    value: function resolve(possibleOverloads, typeParametersInScope, typeArguments) {
      if (!possibleOverloads) throw new WTypeError(this.origin.originString, "Did not find any functions named " + this.name);
      var overload = null;
      var failures = [];
      var _iterator = _createForOfIteratorHelper(typeParametersInScope),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var _typeParameter = _step.value;
          if (!(_typeParameter instanceof TypeVariable)) continue;
          if (!_typeParameter.protocol) continue;
          var signatures = _typeParameter.protocol.protocolDecl.signaturesByNameWithTypeVariable(this.name, _typeParameter);
          if (!signatures) continue;
          overload = resolveOverloadImpl(signatures, this.typeArguments, this.argumentTypes, this.returnType);
          if (overload.func) break;
          failures.push.apply(failures, _toConsumableArray(overload.failures));
          overload = null;
        }
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
      if (!overload) {
        overload = resolveOverloadImpl(possibleOverloads, this.typeArguments, this.argumentTypes, this.returnType);
        if (!overload.func) {
          failures.push.apply(failures, _toConsumableArray(overload.failures));
          var message = "Did not find function named " + this.name + " for call with ";
          if (this.typeArguments.length) message += "type arguments <" + this.typeArguments + "> and ";
          message += "argument types (" + this.argumentTypes + ")";
          if (this.returnType) message += " and return type " + this.returnType;
          if (failures.length) message += ", but considered:\n" + failures.join("\n");
          throw new WTypeError(this.origin.originString, message);
        }
      }
      for (var i = 0; i < typeArguments.length; ++i) {
        var typeArgumentType = typeArguments[i];
        var typeParameter = overload.func.typeParameters[i];
        if (!(typeParameter instanceof ConstexprTypeParameter)) continue;
        if (!typeParameter.type.equalsWithCommit(typeArgumentType)) throw new Error("At " + this.origin.originString + " constexpr type argument and parameter types not equal: argument = " + typeArgumentType + ", parameter = " + typeParameter.type);
      }
      for (var _i = 0; _i < this.argumentTypes.length; ++_i) {
        var argumentType = this.argumentTypes[_i];
        var parameterType = overload.func.parameters[_i].type.substituteToUnification(overload.func.typeParameters, overload.unificationContext);
        var result = argumentType.equalsWithCommit(parameterType);
        if (!result) throw new Error("At " + this.origin.originString + " argument and parameter types not equal after type argument substitution: argument = " + argumentType + ", parameter = " + parameterType);
      }
      return this.resolveToOverload(overload);
    }
  }, {
    key: "resolveToOverload",
    value: function resolveToOverload(overload) {
      this.func = overload.func;
      this.actualTypeArguments = overload.typeArguments.map(function (typeArgument) {
        return typeArgument instanceof Type ? typeArgument.visit(new AutoWrapper()) : typeArgument;
      });
      this.instantiatedActualTypeArguments = this.actualTypeArguments;
      var result = overload.func.returnType.substituteToUnification(overload.func.typeParameters, overload.unificationContext);
      if (!result) throw new Error("Null return type");
      result = result.visit(new AutoWrapper());
      this.resultType = result;
      return result;
    }
  }, {
    key: "becomeCast",
    value: function becomeCast(returnType) {
      this._returnType = new TypeRef(this.origin, this.name, this._typeArguments);
      this._returnType.type = returnType;
      this._name = "operator cast";
      this._isCast = true;
      this._typeArguments = [];
    }
  }, {
    key: "setCastData",
    value: function setCastData(returnType) {
      this._returnType = returnType;
      this._isCast = true;
    }
  }, {
    key: "toString",
    value: function toString() {
      return (this.isCast ? "operator " + this.returnType : this.name) + "<" + this.typeArguments + ">" + (this.actualTypeArguments ? "<<" + this.actualTypeArguments + ">>" : "") + "(" + this.argumentList + ")";
    }
  }], [{
    key: "resolve",
    value: function resolve(origin, possibleOverloads, typeParametersInScope, name, typeArguments, argumentList, argumentTypes, returnType) {
      var call = new CallExpression(origin, name, typeArguments, argumentList);
      call.argumentTypes = argumentTypes.map(function (argument) {
        return argument.visit(new AutoWrapper());
      });
      call.possibleOverloads = possibleOverloads;
      if (returnType) call.setCastData(returnType);
      return {
        call: call,
        resultType: call.resolve(possibleOverloads, typeParametersInScope, typeArguments)
      };
    }
  }]);
}(Expression);