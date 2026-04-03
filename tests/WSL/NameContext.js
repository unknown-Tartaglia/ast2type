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
function _regenerator() { /*! regenerator-runtime -- Copyright (c) 2014-present, Facebook, Inc. -- license (MIT): https://github.com/babel/babel/blob/main/packages/babel-helpers/LICENSE */ var e, t, r = "function" == typeof Symbol ? Symbol : {}, n = r.iterator || "@@iterator", o = r.toStringTag || "@@toStringTag"; function i(r, n, o, i) { var c = n && n.prototype instanceof Generator ? n : Generator, u = Object.create(c.prototype); return _regeneratorDefine2(u, "_invoke", function (r, n, o) { var i, c, u, f = 0, p = o || [], y = !1, G = { p: 0, n: 0, v: e, a: d, f: d.bind(e, 4), d: function d(t, r) { return i = t, c = 0, u = e, G.n = r, a; } }; function d(r, n) { for (c = r, u = n, t = 0; !y && f && !o && t < p.length; t++) { var o, i = p[t], d = G.p, l = i[2]; r > 3 ? (o = l === n) && (u = i[(c = i[4]) ? 5 : (c = 3, 3)], i[4] = i[5] = e) : i[0] <= d && ((o = r < 2 && d < i[1]) ? (c = 0, G.v = n, G.n = i[1]) : d < l && (o = r < 3 || i[0] > n || n > l) && (i[4] = r, i[5] = n, G.n = l, c = 0)); } if (o || r > 1) return a; throw y = !0, n; } return function (o, p, l) { if (f > 1) throw TypeError("Generator is already running"); for (y && 1 === p && d(p, l), c = p, u = l; (t = c < 2 ? e : u) || !y;) { i || (c ? c < 3 ? (c > 1 && (G.n = -1), d(c, u)) : G.n = u : G.v = u); try { if (f = 2, i) { if (c || (o = "next"), t = i[o]) { if (!(t = t.call(i, u))) throw TypeError("iterator result is not an object"); if (!t.done) return t; u = t.value, c < 2 && (c = 0); } else 1 === c && (t = i.return) && t.call(i), c < 2 && (u = TypeError("The iterator does not provide a '" + o + "' method"), c = 1); i = e; } else if ((t = (y = G.n < 0) ? u : r.call(n, G)) !== a) break; } catch (t) { i = e, c = 1, u = t; } finally { f = 1; } } return { value: t, done: y }; }; }(r, o, i), !0), u; } var a = {}; function Generator() {} function GeneratorFunction() {} function GeneratorFunctionPrototype() {} t = Object.getPrototypeOf; var c = [][n] ? t(t([][n]())) : (_regeneratorDefine2(t = {}, n, function () { return this; }), t), u = GeneratorFunctionPrototype.prototype = Generator.prototype = Object.create(c); function f(e) { return Object.setPrototypeOf ? Object.setPrototypeOf(e, GeneratorFunctionPrototype) : (e.__proto__ = GeneratorFunctionPrototype, _regeneratorDefine2(e, o, "GeneratorFunction")), e.prototype = Object.create(u), e; } return GeneratorFunction.prototype = GeneratorFunctionPrototype, _regeneratorDefine2(u, "constructor", GeneratorFunctionPrototype), _regeneratorDefine2(GeneratorFunctionPrototype, "constructor", GeneratorFunction), GeneratorFunction.displayName = "GeneratorFunction", _regeneratorDefine2(GeneratorFunctionPrototype, o, "GeneratorFunction"), _regeneratorDefine2(u), _regeneratorDefine2(u, o, "Generator"), _regeneratorDefine2(u, n, function () { return this; }), _regeneratorDefine2(u, "toString", function () { return "[object Generator]"; }), (_regenerator = function _regenerator() { return { w: i, m: f }; })(); }
function _regeneratorDefine2(e, r, n, t) { var i = Object.defineProperty; try { i({}, "", {}); } catch (e) { i = 0; } _regeneratorDefine2 = function _regeneratorDefine(e, r, n, t) { function o(r, n) { _regeneratorDefine2(e, r, function (e) { return this._invoke(r, n, e); }); } r ? i ? i(e, r, { value: n, enumerable: !t, configurable: !t, writable: !t }) : e[r] = n : (o("next", 0), o("throw", 1), o("return", 2)); }, _regeneratorDefine2(e, r, n, t); }
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
var Anything = Symbol();
function isWildcardKind(kind) {
  return kind == Anything;
}
var NameContext = /*#__PURE__*/function () {
  function NameContext(delegate) {
    _classCallCheck(this, NameContext);
    this._map = new Map();
    this._set = new Set();
    this._currentStatement = null;
    this._delegate = delegate;
    this._intrinsics = null;
    this._program = null;
  }
  return _createClass(NameContext, [{
    key: "add",
    value: function add(thing) {
      if (!thing.name) return;
      if (!thing.origin) throw new Error("Thing does not have origin: " + thing);
      if (thing.isNative && !thing.implementation) {
        if (!this._intrinsics) throw new Error("Native function in a scope that does not recognize intrinsics");
        this._intrinsics.add(thing);
      }
      if (thing.kind == Func) {
        this._set.add(thing);
        var array = this._map.get(thing.name);
        if (!array) {
          array = [];
          array.kind = Func;
          this._map.set(thing.name, array);
        }
        if (array.kind != Func) throw new WTypeError(thing.origin.originString, "Cannot reuse type name for function: " + thing.name);
        array.push(thing);
        return;
      }
      if (this._map.has(thing.name)) throw new WTypeError(thing.origin.originString, "Duplicate name: " + thing.name);
      this._set.add(thing);
      this._map.set(thing.name, thing);
    }
  }, {
    key: "get",
    value: function get(kind, name) {
      var result = this._map.get(name);
      if (!result && this._delegate) return this._delegate.get(kind, name);
      if (result && !isWildcardKind(kind) && result.kind != kind) return null;
      return result;
    }
  }, {
    key: "underlyingThings",
    value: function underlyingThings(kind, name) {
      var things = this.get(kind, name);
      return NameContext.underlyingThings(things);
    }
  }, {
    key: "resolveFuncOverload",
    value: function resolveFuncOverload(name, typeArguments, argumentTypes, returnType) {
      var allowEntryPoint = arguments.length > 4 && arguments[4] !== undefined ? arguments[4] : false;
      var functions = this.get(Func, name);
      if (!functions) return {
        failures: []
      };
      return resolveOverloadImpl(functions, typeArguments, argumentTypes, returnType, allowEntryPoint);
    }
  }, {
    key: "currentStatement",
    get: function get() {
      if (this._currentStatement) return this._currentStatement;
      if (this._delegate) return this._delegate.currentStatement;
      return null;
    }
  }, {
    key: "doStatement",
    value: function doStatement(statement, callback) {
      this._currentStatement = statement;
      callback();
      this._currentStatement = null;
    }
  }, {
    key: "recognizeIntrinsics",
    value: function recognizeIntrinsics() {
      this._intrinsics = new Intrinsics(this);
    }
  }, {
    key: "intrinsics",
    get: function get() {
      if (this._intrinsics) return this._intrinsics;
      if (this._delegate) return this._delegate.intrinsics;
      return null;
    }
  }, {
    key: "program",
    get: function get() {
      if (this._program) return this._program;
      if (this._delegate) return this._delegate.program;
      return null;
    },
    set: function set(value) {
      this._program = value;
    }
  }, {
    key: Symbol.iterator,
    value: /*#__PURE__*/_regenerator().m(function value() {
      var _iterator, _step, value, _iterator2, _step2, func, _t, _t2;
      return _regenerator().w(function (_context) {
        while (1) switch (_context.p = _context.n) {
          case 0:
            _iterator = _createForOfIteratorHelper(this._map.values());
            _context.p = 1;
            _iterator.s();
          case 2:
            if ((_step = _iterator.n()).done) {
              _context.n = 12;
              break;
            }
            value = _step.value;
            if (!(value instanceof Array)) {
              _context.n = 10;
              break;
            }
            _iterator2 = _createForOfIteratorHelper(value);
            _context.p = 3;
            _iterator2.s();
          case 4:
            if ((_step2 = _iterator2.n()).done) {
              _context.n = 6;
              break;
            }
            func = _step2.value;
            _context.n = 5;
            return func;
          case 5:
            _context.n = 4;
            break;
          case 6:
            _context.n = 8;
            break;
          case 7:
            _context.p = 7;
            _t = _context.v;
            _iterator2.e(_t);
          case 8:
            _context.p = 8;
            _iterator2.f();
            return _context.f(8);
          case 9:
            return _context.a(3, 11);
          case 10:
            _context.n = 11;
            return value;
          case 11:
            _context.n = 2;
            break;
          case 12:
            _context.n = 14;
            break;
          case 13:
            _context.p = 13;
            _t2 = _context.v;
            _iterator.e(_t2);
          case 14:
            _context.p = 14;
            _iterator.f();
            return _context.f(14);
          case 15:
            return _context.a(2);
        }
      }, value, this, [[3, 7, 8, 9], [1, 13, 14, 15]]);
    })
  }], [{
    key: "underlyingThings",
    value: /*#__PURE__*/_regenerator().m(function underlyingThings(thing) {
      var _iterator3, _step3, func, _t3;
      return _regenerator().w(function (_context2) {
        while (1) switch (_context2.p = _context2.n) {
          case 0:
            if (thing) {
              _context2.n = 1;
              break;
            }
            return _context2.a(2);
          case 1:
            if (!(thing.kind === Func)) {
              _context2.n = 10;
              break;
            }
            if (thing instanceof Array) {
              _context2.n = 2;
              break;
            }
            throw new Error("Func thing is not array: " + thing);
          case 2:
            _iterator3 = _createForOfIteratorHelper(thing);
            _context2.p = 3;
            _iterator3.s();
          case 4:
            if ((_step3 = _iterator3.n()).done) {
              _context2.n = 6;
              break;
            }
            func = _step3.value;
            _context2.n = 5;
            return func;
          case 5:
            _context2.n = 4;
            break;
          case 6:
            _context2.n = 8;
            break;
          case 7:
            _context2.p = 7;
            _t3 = _context2.v;
            _iterator3.e(_t3);
          case 8:
            _context2.p = 8;
            _iterator3.f();
            return _context2.f(8);
          case 9:
            return _context2.a(2);
          case 10:
            _context2.n = 11;
            return thing;
          case 11:
            return _context2.a(2);
        }
      }, underlyingThings, null, [[3, 7, 8, 9]]);
    })
  }]);
}();