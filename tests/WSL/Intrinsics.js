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
function _slicedToArray(r, e) { return _arrayWithHoles(r) || _iterableToArrayLimit(r, e) || _unsupportedIterableToArray(r, e) || _nonIterableRest(); }
function _nonIterableRest() { throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function _iterableToArrayLimit(r, l) { var t = null == r ? null : "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (null != t) { var e, n, i, u, a = [], f = !0, o = !1; try { if (i = (t = t.call(r)).next, 0 === l) { if (Object(t) !== t) return; f = !1; } else for (; !(f = (e = i.call(t)).done) && (a.push(e.value), a.length !== l); f = !0); } catch (r) { o = !0, n = r; } finally { try { if (!f && null != t.return && (u = t.return(), Object(u) !== u)) return; } finally { if (o) throw n; } } return a; } }
function _arrayWithHoles(r) { if (Array.isArray(r)) return r; }
function _regenerator() { /*! regenerator-runtime -- Copyright (c) 2014-present, Facebook, Inc. -- license (MIT): https://github.com/babel/babel/blob/main/packages/babel-helpers/LICENSE */ var e, t, r = "function" == typeof Symbol ? Symbol : {}, n = r.iterator || "@@iterator", o = r.toStringTag || "@@toStringTag"; function i(r, n, o, i) { var c = n && n.prototype instanceof Generator ? n : Generator, u = Object.create(c.prototype); return _regeneratorDefine2(u, "_invoke", function (r, n, o) { var i, c, u, f = 0, p = o || [], y = !1, G = { p: 0, n: 0, v: e, a: d, f: d.bind(e, 4), d: function d(t, r) { return i = t, c = 0, u = e, G.n = r, a; } }; function d(r, n) { for (c = r, u = n, t = 0; !y && f && !o && t < p.length; t++) { var o, i = p[t], d = G.p, l = i[2]; r > 3 ? (o = l === n) && (u = i[(c = i[4]) ? 5 : (c = 3, 3)], i[4] = i[5] = e) : i[0] <= d && ((o = r < 2 && d < i[1]) ? (c = 0, G.v = n, G.n = i[1]) : d < l && (o = r < 3 || i[0] > n || n > l) && (i[4] = r, i[5] = n, G.n = l, c = 0)); } if (o || r > 1) return a; throw y = !0, n; } return function (o, p, l) { if (f > 1) throw TypeError("Generator is already running"); for (y && 1 === p && d(p, l), c = p, u = l; (t = c < 2 ? e : u) || !y;) { i || (c ? c < 3 ? (c > 1 && (G.n = -1), d(c, u)) : G.n = u : G.v = u); try { if (f = 2, i) { if (c || (o = "next"), t = i[o]) { if (!(t = t.call(i, u))) throw TypeError("iterator result is not an object"); if (!t.done) return t; u = t.value, c < 2 && (c = 0); } else 1 === c && (t = i.return) && t.call(i), c < 2 && (u = TypeError("The iterator does not provide a '" + o + "' method"), c = 1); i = e; } else if ((t = (y = G.n < 0) ? u : r.call(n, G)) !== a) break; } catch (t) { i = e, c = 1, u = t; } finally { f = 1; } } return { value: t, done: y }; }; }(r, o, i), !0), u; } var a = {}; function Generator() {} function GeneratorFunction() {} function GeneratorFunctionPrototype() {} t = Object.getPrototypeOf; var c = [][n] ? t(t([][n]())) : (_regeneratorDefine2(t = {}, n, function () { return this; }), t), u = GeneratorFunctionPrototype.prototype = Generator.prototype = Object.create(c); function f(e) { return Object.setPrototypeOf ? Object.setPrototypeOf(e, GeneratorFunctionPrototype) : (e.__proto__ = GeneratorFunctionPrototype, _regeneratorDefine2(e, o, "GeneratorFunction")), e.prototype = Object.create(u), e; } return GeneratorFunction.prototype = GeneratorFunctionPrototype, _regeneratorDefine2(u, "constructor", GeneratorFunctionPrototype), _regeneratorDefine2(GeneratorFunctionPrototype, "constructor", GeneratorFunction), GeneratorFunction.displayName = "GeneratorFunction", _regeneratorDefine2(GeneratorFunctionPrototype, o, "GeneratorFunction"), _regeneratorDefine2(u), _regeneratorDefine2(u, o, "Generator"), _regeneratorDefine2(u, n, function () { return this; }), _regeneratorDefine2(u, "toString", function () { return "[object Generator]"; }), (_regenerator = function _regenerator() { return { w: i, m: f }; })(); }
function _regeneratorDefine2(e, r, n, t) { var i = Object.defineProperty; try { i({}, "", {}); } catch (e) { i = 0; } _regeneratorDefine2 = function _regeneratorDefine(e, r, n, t) { function o(r, n) { _regeneratorDefine2(e, r, function (e) { return this._invoke(r, n, e); }); } r ? i ? i(e, r, { value: n, enumerable: !t, configurable: !t, writable: !t }) : e[r] = n : (o("next", 0), o("throw", 1), o("return", 2)); }, _regeneratorDefine2(e, r, n, t); }
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
var Intrinsics = /*#__PURE__*/function () {
  function Intrinsics(nameContext) {
    var _this = this;
    _classCallCheck(this, Intrinsics);
    this._map = new Map();

    // NOTE: Intrinsic resolution happens before type name resolution, so the strings we use here
    // to catch the intrinsics must be based on the type names that StandardLibraryPrologue.js uses.
    // For example, if a native function is declared using "int" rather than "int32", then we must
    // use "int" here, since we don't yet know that they are the same type.

    this._map.set("native typedef void<>", function (type) {
      _this.void = type;
      type.size = 0;
      type.populateDefaultValue = function () {};
    });
    function isBitwiseEquivalent(left, right) {
      var doubleArray = new Float64Array(1);
      var intArray = new Int32Array(doubleArray.buffer);
      doubleArray[0] = left;
      var leftInts = Int32Array.from(intArray);
      doubleArray[0] = right;
      for (var i = 0; i < 2; ++i) {
        if (leftInts[i] != intArray[i]) return false;
      }
      return true;
    }
    this._map.set("native typedef int32<>", function (type) {
      _this.int32 = type;
      type.isPrimitive = true;
      type.isInt = true;
      type.isNumber = true;
      type.isSigned = true;
      type.canRepresent = function (value) {
        return isBitwiseEquivalent(value | 0, value);
      };
      type.size = 1;
      type.defaultValue = 0;
      type.createLiteral = function (origin, value) {
        return IntLiteral.withType(origin, value | 0, type);
      };
      type.successorValue = function (value) {
        return value + 1 | 0;
      };
      type.valuesEqual = function (a, b) {
        return a === b;
      };
      type.populateDefaultValue = function (buffer, offset) {
        return buffer.set(offset, 0);
      };
      type.formatValueFromIntLiteral = function (value) {
        return value | 0;
      };
      type.formatValueFromUintLiteral = function (value) {
        return value | 0;
      };
      type.allValues = /*#__PURE__*/_regenerator().m(function _callee() {
        var i, value;
        return _regenerator().w(function (_context) {
          while (1) switch (_context.n) {
            case 0:
              i = 0;
            case 1:
              if (!(i <= 0xffffffff)) {
                _context.n = 3;
                break;
              }
              value = i | 0;
              _context.n = 2;
              return {
                value: value,
                name: value
              };
            case 2:
              ++i;
              _context.n = 1;
              break;
            case 3:
              return _context.a(2);
          }
        }, _callee);
      });
    });
    this._map.set("native typedef uint32<>", function (type) {
      _this.uint32 = type;
      type.isPrimitive = true;
      type.isInt = true;
      type.isNumber = true;
      type.isSigned = false;
      type.canRepresent = function (value) {
        return isBitwiseEquivalent(value >>> 0, value);
      };
      type.size = 1;
      type.defaultValue = 0;
      type.createLiteral = function (origin, value) {
        return IntLiteral.withType(origin, value >>> 0, type);
      };
      type.successorValue = function (value) {
        return value + 1 >>> 0;
      };
      type.valuesEqual = function (a, b) {
        return a === b;
      };
      type.populateDefaultValue = function (buffer, offset) {
        return buffer.set(offset, 0);
      };
      type.formatValueFromIntLiteral = function (value) {
        return value >>> 0;
      };
      type.formatValueFromUintLiteral = function (value) {
        return value >>> 0;
      };
      type.allValues = /*#__PURE__*/_regenerator().m(function _callee2() {
        var i;
        return _regenerator().w(function (_context2) {
          while (1) switch (_context2.n) {
            case 0:
              i = 0;
            case 1:
              if (!(i <= 0xffffffff)) {
                _context2.n = 3;
                break;
              }
              _context2.n = 2;
              return {
                value: i,
                name: i
              };
            case 2:
              ++i;
              _context2.n = 1;
              break;
            case 3:
              return _context2.a(2);
          }
        }, _callee2);
      });
    });
    this._map.set("native typedef uint8<>", function (type) {
      _this.uint8 = type;
      type.isInt = true;
      type.isNumber = true;
      type.isSigned = false;
      type.canRepresent = function (value) {
        return isBitwiseEquivalent(value & 0xff, value);
      };
      type.size = 1;
      type.defaultValue = 0;
      type.createLiteral = function (origin, value) {
        return IntLiteral.withType(origin, value & 0xff, type);
      };
      type.successorValue = function (value) {
        return value + 1 & 0xff;
      };
      type.valuesEqual = function (a, b) {
        return a === b;
      };
      type.populateDefaultValue = function (buffer, offset) {
        return buffer.set(offset, 0);
      };
      type.formatValueFromIntLiteral = function (value) {
        return value & 0xff;
      };
      type.formatValueFromUintLiteral = function (value) {
        return value & 0xff;
      };
      type.allValues = /*#__PURE__*/_regenerator().m(function _callee3() {
        var i;
        return _regenerator().w(function (_context3) {
          while (1) switch (_context3.n) {
            case 0:
              i = 0;
            case 1:
              if (!(i <= 0xff)) {
                _context3.n = 3;
                break;
              }
              _context3.n = 2;
              return {
                value: i,
                name: i
              };
            case 2:
              ++i;
              _context3.n = 1;
              break;
            case 3:
              return _context3.a(2);
          }
        }, _callee3);
      });
    });
    this._map.set("native typedef float32<>", function (type) {
      _this.float = type;
      type.isPrimitive = true;
      type.size = 1;
      type.isFloating = true;
      type.isNumber = true;
      type.canRepresent = function (value) {
        return isBitwiseEquivalent(Math.fround(value), value);
      };
      type.populateDefaultValue = function (buffer, offset) {
        return buffer.set(offset, 0);
      };
      type.formatValueFromIntLiteral = function (value) {
        return value;
      };
      type.formatValueFromUintLiteral = function (value) {
        return value;
      };
      type.formatValueFromFloatLiteral = function (value) {
        return Math.fround(value);
      };
      type.formatValueFromDoubleLiteral = function (value) {
        return Math.fround(value);
      };
    });
    this._map.set("native typedef float64<>", function (type) {
      _this.double = type;
      type.isPrimitive = true;
      type.size = 1;
      type.isFloating = true;
      type.isNumber = true;
      type.canRepresent = function (value) {
        return true;
      };
      type.populateDefaultValue = function (buffer, offset) {
        return buffer.set(offset, 0);
      };
      type.formatValueFromIntLiteral = function (value) {
        return value;
      };
      type.formatValueFromUintLiteral = function (value) {
        return value;
      };
      type.formatValueFromFloatLiteral = function (value) {
        return value;
      };
      type.formatValueFromDoubleLiteral = function (value) {
        return value;
      };
    });
    this._map.set("native typedef bool<>", function (type) {
      _this.bool = type;
      type.isPrimitive = true;
      type.size = 1;
      type.populateDefaultValue = function (buffer, offset) {
        return buffer.set(offset, false);
      };
    });
    this._map.set("native operator<> int32(uint32)", function (func) {
      func.implementation = function (_ref) {
        var _ref2 = _slicedToArray(_ref, 1),
          value = _ref2[0];
        return EPtr.box(value.loadValue() | 0);
      };
    });
    this._map.set("native operator<> int32(uint8)", function (func) {
      func.implementation = function (_ref3) {
        var _ref4 = _slicedToArray(_ref3, 1),
          value = _ref4[0];
        return EPtr.box(value.loadValue() | 0);
      };
    });
    this._map.set("native operator<> int32(float)", function (func) {
      func.implementation = function (_ref5) {
        var _ref6 = _slicedToArray(_ref5, 1),
          value = _ref6[0];
        return EPtr.box(value.loadValue() | 0);
      };
    });
    this._map.set("native operator<> int32(double)", function (func) {
      func.implementation = function (_ref7) {
        var _ref8 = _slicedToArray(_ref7, 1),
          value = _ref8[0];
        return EPtr.box(value.loadValue() | 0);
      };
    });
    this._map.set("native operator<> uint32(int32)", function (func) {
      func.implementation = function (_ref9) {
        var _ref0 = _slicedToArray(_ref9, 1),
          value = _ref0[0];
        return EPtr.box(value.loadValue() >>> 0);
      };
    });
    this._map.set("native operator<> uint32(uint8)", function (func) {
      func.implementation = function (_ref1) {
        var _ref10 = _slicedToArray(_ref1, 1),
          value = _ref10[0];
        return EPtr.box(value.loadValue() >>> 0);
      };
    });
    this._map.set("native operator<> uint32(float)", function (func) {
      func.implementation = function (_ref11) {
        var _ref12 = _slicedToArray(_ref11, 1),
          value = _ref12[0];
        return EPtr.box(value.loadValue() >>> 0);
      };
    });
    this._map.set("native operator<> uint32(double)", function (func) {
      func.implementation = function (_ref13) {
        var _ref14 = _slicedToArray(_ref13, 1),
          value = _ref14[0];
        return EPtr.box(value.loadValue() >>> 0);
      };
    });
    this._map.set("native operator<> uint8(int32)", function (func) {
      func.implementation = function (_ref15) {
        var _ref16 = _slicedToArray(_ref15, 1),
          value = _ref16[0];
        return EPtr.box(value.loadValue() & 0xff);
      };
    });
    this._map.set("native operator<> uint8(uint32)", function (func) {
      func.implementation = function (_ref17) {
        var _ref18 = _slicedToArray(_ref17, 1),
          value = _ref18[0];
        return EPtr.box(value.loadValue() & 0xff);
      };
    });
    this._map.set("native operator<> uint8(float)", function (func) {
      func.implementation = function (_ref19) {
        var _ref20 = _slicedToArray(_ref19, 1),
          value = _ref20[0];
        return EPtr.box(value.loadValue() & 0xff);
      };
    });
    this._map.set("native operator<> uint8(double)", function (func) {
      func.implementation = function (_ref21) {
        var _ref22 = _slicedToArray(_ref21, 1),
          value = _ref22[0];
        return EPtr.box(value.loadValue() & 0xff);
      };
    });
    this._map.set("native operator<> float(double)", function (func) {
      func.implementation = function (_ref23) {
        var _ref24 = _slicedToArray(_ref23, 1),
          value = _ref24[0];
        return EPtr.box(Math.fround(value.loadValue()));
      };
    });
    this._map.set("native operator<> float(int32)", function (func) {
      func.implementation = function (_ref25) {
        var _ref26 = _slicedToArray(_ref25, 1),
          value = _ref26[0];
        return EPtr.box(Math.fround(value.loadValue()));
      };
    });
    this._map.set("native operator<> float(uint32)", function (func) {
      func.implementation = function (_ref27) {
        var _ref28 = _slicedToArray(_ref27, 1),
          value = _ref28[0];
        return EPtr.box(Math.fround(value.loadValue()));
      };
    });
    this._map.set("native operator<> float(uint8)", function (func) {
      func.implementation = function (_ref29) {
        var _ref30 = _slicedToArray(_ref29, 1),
          value = _ref30[0];
        return EPtr.box(Math.fround(value.loadValue()));
      };
    });
    this._map.set("native operator<> double(float)", function (func) {
      func.implementation = function (_ref31) {
        var _ref32 = _slicedToArray(_ref31, 1),
          value = _ref32[0];
        return EPtr.box(value.loadValue());
      };
    });
    this._map.set("native operator<> double(int32)", function (func) {
      func.implementation = function (_ref33) {
        var _ref34 = _slicedToArray(_ref33, 1),
          value = _ref34[0];
        return EPtr.box(value.loadValue());
      };
    });
    this._map.set("native operator<> double(uint32)", function (func) {
      func.implementation = function (_ref35) {
        var _ref36 = _slicedToArray(_ref35, 1),
          value = _ref36[0];
        return EPtr.box(value.loadValue());
      };
    });
    this._map.set("native operator<> double(uint8)", function (func) {
      func.implementation = function (_ref37) {
        var _ref38 = _slicedToArray(_ref37, 1),
          value = _ref38[0];
        return EPtr.box(value.loadValue());
      };
    });
    this._map.set("native int operator+<>(int,int)", function (func) {
      func.implementation = function (_ref39) {
        var _ref40 = _slicedToArray(_ref39, 2),
          left = _ref40[0],
          right = _ref40[1];
        return EPtr.box(left.loadValue() + right.loadValue() | 0);
      };
    });
    this._map.set("native uint operator+<>(uint,uint)", function (func) {
      func.implementation = function (_ref41) {
        var _ref42 = _slicedToArray(_ref41, 2),
          left = _ref42[0],
          right = _ref42[1];
        return EPtr.box(left.loadValue() + right.loadValue() >>> 0);
      };
    });
    this._map.set("native float operator+<>(float,float)", function (func) {
      func.implementation = function (_ref43) {
        var _ref44 = _slicedToArray(_ref43, 2),
          left = _ref44[0],
          right = _ref44[1];
        return EPtr.box(Math.fround(left.loadValue() + right.loadValue()));
      };
    });
    this._map.set("native double operator+<>(double,double)", function (func) {
      func.implementation = function (_ref45) {
        var _ref46 = _slicedToArray(_ref45, 2),
          left = _ref46[0],
          right = _ref46[1];
        return EPtr.box(left.loadValue() + right.loadValue());
      };
    });
    this._map.set("native int operator-<>(int,int)", function (func) {
      func.implementation = function (_ref47) {
        var _ref48 = _slicedToArray(_ref47, 2),
          left = _ref48[0],
          right = _ref48[1];
        return EPtr.box(left.loadValue() - right.loadValue() | 0);
      };
    });
    this._map.set("native uint operator-<>(uint,uint)", function (func) {
      func.implementation = function (_ref49) {
        var _ref50 = _slicedToArray(_ref49, 2),
          left = _ref50[0],
          right = _ref50[1];
        return EPtr.box(left.loadValue() - right.loadValue() >>> 0);
      };
    });
    this._map.set("native float operator-<>(float,float)", function (func) {
      func.implementation = function (_ref51) {
        var _ref52 = _slicedToArray(_ref51, 2),
          left = _ref52[0],
          right = _ref52[1];
        return EPtr.box(Math.fround(left.loadValue() - right.loadValue()));
      };
    });
    this._map.set("native double operator-<>(double,double)", function (func) {
      func.implementation = function (_ref53) {
        var _ref54 = _slicedToArray(_ref53, 2),
          left = _ref54[0],
          right = _ref54[1];
        return EPtr.box(left.loadValue() - right.loadValue());
      };
    });
    this._map.set("native int operator*<>(int,int)", function (func) {
      func.implementation = function (_ref55) {
        var _ref56 = _slicedToArray(_ref55, 2),
          left = _ref56[0],
          right = _ref56[1];
        return EPtr.box(left.loadValue() * right.loadValue() | 0);
      };
    });
    this._map.set("native uint operator*<>(uint,uint)", function (func) {
      func.implementation = function (_ref57) {
        var _ref58 = _slicedToArray(_ref57, 2),
          left = _ref58[0],
          right = _ref58[1];
        return EPtr.box(left.loadValue() * right.loadValue() >>> 0);
      };
    });
    this._map.set("native float operator*<>(float,float)", function (func) {
      func.implementation = function (_ref59) {
        var _ref60 = _slicedToArray(_ref59, 2),
          left = _ref60[0],
          right = _ref60[1];
        return EPtr.box(Math.fround(left.loadValue() * right.loadValue()));
      };
    });
    this._map.set("native double operator*<>(double,double)", function (func) {
      func.implementation = function (_ref61) {
        var _ref62 = _slicedToArray(_ref61, 2),
          left = _ref62[0],
          right = _ref62[1];
        return EPtr.box(left.loadValue() * right.loadValue());
      };
    });
    this._map.set("native int operator/<>(int,int)", function (func) {
      func.implementation = function (_ref63) {
        var _ref64 = _slicedToArray(_ref63, 2),
          left = _ref64[0],
          right = _ref64[1];
        return EPtr.box(left.loadValue() / right.loadValue() | 0);
      };
    });
    this._map.set("native uint operator/<>(uint,uint)", function (func) {
      func.implementation = function (_ref65) {
        var _ref66 = _slicedToArray(_ref65, 2),
          left = _ref66[0],
          right = _ref66[1];
        return EPtr.box(left.loadValue() / right.loadValue() >>> 0);
      };
    });
    this._map.set("native int operator&<>(int,int)", function (func) {
      func.implementation = function (_ref67) {
        var _ref68 = _slicedToArray(_ref67, 2),
          left = _ref68[0],
          right = _ref68[1];
        return EPtr.box(left.loadValue() & right.loadValue());
      };
    });
    this._map.set("native uint operator&<>(uint,uint)", function (func) {
      func.implementation = function (_ref69) {
        var _ref70 = _slicedToArray(_ref69, 2),
          left = _ref70[0],
          right = _ref70[1];
        return EPtr.box((left.loadValue() & right.loadValue()) >>> 0);
      };
    });
    this._map.set("native int operator|<>(int,int)", function (func) {
      func.implementation = function (_ref71) {
        var _ref72 = _slicedToArray(_ref71, 2),
          left = _ref72[0],
          right = _ref72[1];
        return EPtr.box(left.loadValue() | right.loadValue());
      };
    });
    this._map.set("native uint operator|<>(uint,uint)", function (func) {
      func.implementation = function (_ref73) {
        var _ref74 = _slicedToArray(_ref73, 2),
          left = _ref74[0],
          right = _ref74[1];
        return EPtr.box((left.loadValue() | right.loadValue()) >>> 0);
      };
    });
    this._map.set("native int operator^<>(int,int)", function (func) {
      func.implementation = function (_ref75) {
        var _ref76 = _slicedToArray(_ref75, 2),
          left = _ref76[0],
          right = _ref76[1];
        return EPtr.box(left.loadValue() ^ right.loadValue());
      };
    });
    this._map.set("native uint operator^<>(uint,uint)", function (func) {
      func.implementation = function (_ref77) {
        var _ref78 = _slicedToArray(_ref77, 2),
          left = _ref78[0],
          right = _ref78[1];
        return EPtr.box((left.loadValue() ^ right.loadValue()) >>> 0);
      };
    });
    this._map.set("native int operator<<<>(int,uint)", function (func) {
      func.implementation = function (_ref79) {
        var _ref80 = _slicedToArray(_ref79, 2),
          left = _ref80[0],
          right = _ref80[1];
        return EPtr.box(left.loadValue() << right.loadValue());
      };
    });
    this._map.set("native uint operator<<<>(uint,uint)", function (func) {
      func.implementation = function (_ref81) {
        var _ref82 = _slicedToArray(_ref81, 2),
          left = _ref82[0],
          right = _ref82[1];
        return EPtr.box(left.loadValue() << right.loadValue() >>> 0);
      };
    });
    this._map.set("native int operator>><>(int,uint)", function (func) {
      func.implementation = function (_ref83) {
        var _ref84 = _slicedToArray(_ref83, 2),
          left = _ref84[0],
          right = _ref84[1];
        return EPtr.box(left.loadValue() >> right.loadValue());
      };
    });
    this._map.set("native uint operator>><>(uint,uint)", function (func) {
      func.implementation = function (_ref85) {
        var _ref86 = _slicedToArray(_ref85, 2),
          left = _ref86[0],
          right = _ref86[1];
        return EPtr.box(left.loadValue() >>> right.loadValue());
      };
    });
    this._map.set("native int operator~<>(int)", function (func) {
      func.implementation = function (_ref87) {
        var _ref88 = _slicedToArray(_ref87, 1),
          value = _ref88[0];
        return EPtr.box(~value.loadValue());
      };
    });
    this._map.set("native uint operator~<>(uint)", function (func) {
      func.implementation = function (_ref89) {
        var _ref90 = _slicedToArray(_ref89, 1),
          value = _ref90[0];
        return EPtr.box(~value.loadValue() >>> 0);
      };
    });
    this._map.set("native float operator/<>(float,float)", function (func) {
      func.implementation = function (_ref91) {
        var _ref92 = _slicedToArray(_ref91, 2),
          left = _ref92[0],
          right = _ref92[1];
        return EPtr.box(Math.fround(left.loadValue() / right.loadValue()));
      };
    });
    this._map.set("native double operator/<>(double,double)", function (func) {
      func.implementation = function (_ref93) {
        var _ref94 = _slicedToArray(_ref93, 2),
          left = _ref94[0],
          right = _ref94[1];
        return EPtr.box(left.loadValue() / right.loadValue());
      };
    });
    this._map.set("native bool operator==<>(int,int)", function (func) {
      func.implementation = function (_ref95) {
        var _ref96 = _slicedToArray(_ref95, 2),
          left = _ref96[0],
          right = _ref96[1];
        return EPtr.box(left.loadValue() == right.loadValue());
      };
    });
    this._map.set("native bool operator==<>(uint,uint)", function (func) {
      func.implementation = function (_ref97) {
        var _ref98 = _slicedToArray(_ref97, 2),
          left = _ref98[0],
          right = _ref98[1];
        return EPtr.box(left.loadValue() == right.loadValue());
      };
    });
    this._map.set("native bool operator==<>(bool,bool)", function (func) {
      func.implementation = function (_ref99) {
        var _ref100 = _slicedToArray(_ref99, 2),
          left = _ref100[0],
          right = _ref100[1];
        return EPtr.box(left.loadValue() == right.loadValue());
      };
    });
    this._map.set("native bool operator==<>(float,float)", function (func) {
      func.implementation = function (_ref101) {
        var _ref102 = _slicedToArray(_ref101, 2),
          left = _ref102[0],
          right = _ref102[1];
        return EPtr.box(left.loadValue() == right.loadValue());
      };
    });
    this._map.set("native bool operator==<>(double,double)", function (func) {
      func.implementation = function (_ref103) {
        var _ref104 = _slicedToArray(_ref103, 2),
          left = _ref104[0],
          right = _ref104[1];
        return EPtr.box(left.loadValue() == right.loadValue());
      };
    });
    this._map.set("native bool operator<<>(int,int)", function (func) {
      func.implementation = function (_ref105) {
        var _ref106 = _slicedToArray(_ref105, 2),
          left = _ref106[0],
          right = _ref106[1];
        return EPtr.box(left.loadValue() < right.loadValue());
      };
    });
    this._map.set("native bool operator<<>(uint,uint)", function (func) {
      func.implementation = function (_ref107) {
        var _ref108 = _slicedToArray(_ref107, 2),
          left = _ref108[0],
          right = _ref108[1];
        return EPtr.box(left.loadValue() < right.loadValue());
      };
    });
    this._map.set("native bool operator<<>(float,float)", function (func) {
      func.implementation = function (_ref109) {
        var _ref110 = _slicedToArray(_ref109, 2),
          left = _ref110[0],
          right = _ref110[1];
        return EPtr.box(left.loadValue() < right.loadValue());
      };
    });
    this._map.set("native bool operator<<>(double,double)", function (func) {
      func.implementation = function (_ref111) {
        var _ref112 = _slicedToArray(_ref111, 2),
          left = _ref112[0],
          right = _ref112[1];
        return EPtr.box(left.loadValue() < right.loadValue());
      };
    });
    this._map.set("native bool operator<=<>(int,int)", function (func) {
      func.implementation = function (_ref113) {
        var _ref114 = _slicedToArray(_ref113, 2),
          left = _ref114[0],
          right = _ref114[1];
        return EPtr.box(left.loadValue() <= right.loadValue());
      };
    });
    this._map.set("native bool operator<=<>(uint,uint)", function (func) {
      func.implementation = function (_ref115) {
        var _ref116 = _slicedToArray(_ref115, 2),
          left = _ref116[0],
          right = _ref116[1];
        return EPtr.box(left.loadValue() <= right.loadValue());
      };
    });
    this._map.set("native bool operator<=<>(float,float)", function (func) {
      func.implementation = function (_ref117) {
        var _ref118 = _slicedToArray(_ref117, 2),
          left = _ref118[0],
          right = _ref118[1];
        return EPtr.box(left.loadValue() <= right.loadValue());
      };
    });
    this._map.set("native bool operator<=<>(double,double)", function (func) {
      func.implementation = function (_ref119) {
        var _ref120 = _slicedToArray(_ref119, 2),
          left = _ref120[0],
          right = _ref120[1];
        return EPtr.box(left.loadValue() <= right.loadValue());
      };
    });
    this._map.set("native bool operator><>(int,int)", function (func) {
      func.implementation = function (_ref121) {
        var _ref122 = _slicedToArray(_ref121, 2),
          left = _ref122[0],
          right = _ref122[1];
        return EPtr.box(left.loadValue() > right.loadValue());
      };
    });
    this._map.set("native bool operator><>(uint,uint)", function (func) {
      func.implementation = function (_ref123) {
        var _ref124 = _slicedToArray(_ref123, 2),
          left = _ref124[0],
          right = _ref124[1];
        return EPtr.box(left.loadValue() > right.loadValue());
      };
    });
    this._map.set("native bool operator><>(float,float)", function (func) {
      func.implementation = function (_ref125) {
        var _ref126 = _slicedToArray(_ref125, 2),
          left = _ref126[0],
          right = _ref126[1];
        return EPtr.box(left.loadValue() > right.loadValue());
      };
    });
    this._map.set("native bool operator><>(double,double)", function (func) {
      func.implementation = function (_ref127) {
        var _ref128 = _slicedToArray(_ref127, 2),
          left = _ref128[0],
          right = _ref128[1];
        return EPtr.box(left.loadValue() > right.loadValue());
      };
    });
    this._map.set("native bool operator>=<>(int,int)", function (func) {
      func.implementation = function (_ref129) {
        var _ref130 = _slicedToArray(_ref129, 2),
          left = _ref130[0],
          right = _ref130[1];
        return EPtr.box(left.loadValue() >= right.loadValue());
      };
    });
    this._map.set("native bool operator>=<>(uint,uint)", function (func) {
      func.implementation = function (_ref131) {
        var _ref132 = _slicedToArray(_ref131, 2),
          left = _ref132[0],
          right = _ref132[1];
        return EPtr.box(left.loadValue() >= right.loadValue());
      };
    });
    this._map.set("native bool operator>=<>(float,float)", function (func) {
      func.implementation = function (_ref133) {
        var _ref134 = _slicedToArray(_ref133, 2),
          left = _ref134[0],
          right = _ref134[1];
        return EPtr.box(left.loadValue() >= right.loadValue());
      };
    });
    this._map.set("native bool operator>=<>(double,double)", function (func) {
      func.implementation = function (_ref135) {
        var _ref136 = _slicedToArray(_ref135, 2),
          left = _ref136[0],
          right = _ref136[1];
        return EPtr.box(left.loadValue() >= right.loadValue());
      };
    });
    var _iterator = _createForOfIteratorHelper(addressSpaces),
      _step;
    try {
      for (_iterator.s(); !(_step = _iterator.n()).done;) {
        var addressSpace = _step.value;
        this._map.set("native T* ".concat(addressSpace, " operator&[]<T>(T[] ").concat(addressSpace, ",uint)"), function (func) {
          func.implementation = function (_ref137, node) {
            var _ref138 = _slicedToArray(_ref137, 2),
              ref = _ref138[0],
              index = _ref138[1];
            ref = ref.loadValue();
            if (!ref) throw new WTrapError(node.origin.originString, "Null dereference");
            index = index.loadValue();
            if (index > ref.length) throw new WTrapError(node.origin.originString, "Array index " + index + " is out of bounds of " + ref);
            return EPtr.box(ref.ptr.plus(index * node.instantiatedActualTypeArguments[0].size));
          };
        });
        this._map.set("native uint operator.length<T>(T[] ".concat(addressSpace, ")"), function (func) {
          func.implementation = function (_ref139, node) {
            var _ref140 = _slicedToArray(_ref139, 1),
              ref = _ref140[0];
            ref = ref.loadValue();
            if (!ref) return EPtr.box(0);
            return EPtr.box(ref.length);
          };
        });
      }
    } catch (err) {
      _iterator.e(err);
    } finally {
      _iterator.f();
    }
  }
  return _createClass(Intrinsics, [{
    key: "add",
    value: function add(thing) {
      var intrinsic = this._map.get(thing.toString());
      if (!intrinsic) throw new WTypeError(thing.origin.originString, "Unrecognized intrinsic: " + thing);
      intrinsic(thing);
    }
  }]);
}();