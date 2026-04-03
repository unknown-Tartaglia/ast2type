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
function _superPropGet(t, o, e, r) { var p = _get(_getPrototypeOf(1 & r ? t.prototype : t), o, e); return 2 & r && "function" == typeof p ? function (t) { return p.apply(e, t); } : p; }
function _get() { return _get = "undefined" != typeof Reflect && Reflect.get ? Reflect.get.bind() : function (e, t, r) { var p = _superPropBase(e, t); if (p) { var n = Object.getOwnPropertyDescriptor(p, t); return n.get ? n.get.call(arguments.length < 3 ? e : r) : n.value; } }, _get.apply(null, arguments); }
function _superPropBase(t, o) { for (; !{}.hasOwnProperty.call(t, o) && null !== (t = _getPrototypeOf(t));); return t; }
function _getPrototypeOf(t) { return _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function (t) { return t.__proto__ || Object.getPrototypeOf(t); }, _getPrototypeOf(t); }
function _inherits(t, e) { if ("function" != typeof e && null !== e) throw new TypeError("Super expression must either be null or a function"); t.prototype = Object.create(e && e.prototype, { constructor: { value: t, writable: !0, configurable: !0 } }), Object.defineProperty(t, "prototype", { writable: !1 }), e && _setPrototypeOf(t, e); }
function _setPrototypeOf(t, e) { return _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function (t, e) { return t.__proto__ = e, t; }, _setPrototypeOf(t, e); }
var SPIRVPrimitiveVariableAnalyzer = /*#__PURE__*/function (_Visitor) {
  function SPIRVPrimitiveVariableAnalyzer(program, typeMap, currentId, currentLocation, startName) {
    var _this;
    _classCallCheck(this, SPIRVPrimitiveVariableAnalyzer);
    _this = _callSuper(this, SPIRVPrimitiveVariableAnalyzer);
    _this._program = program;
    _this._typeMap = typeMap;
    _this._currentId = currentId;
    _this._currentLocation = currentLocation;
    _this._nameComponents = [];
    if (startName) _this._nameComponents.push(startName);
    _this._result = [];
    return _this;
  }
  _inherits(SPIRVPrimitiveVariableAnalyzer, _Visitor);
  return _createClass(SPIRVPrimitiveVariableAnalyzer, [{
    key: "program",
    get: function get() {
      this._program;
    }
  }, {
    key: "typeMap",
    get: function get() {
      return this._typeMap;
    }
  }, {
    key: "currentId",
    get: function get() {
      return this._currentId;
    }
  }, {
    key: "currentLocation",
    get: function get() {
      return this._currentLocation;
    }
  }, {
    key: "nameComponents",
    get: function get() {
      return this._nameComponents;
    }
  }, {
    key: "result",
    get: function get() {
      return this._result;
    }
  }, {
    key: "visitTypeRef",
    value: function visitTypeRef(node) {
      node.type.visit(this);
    }
  }, {
    key: "visitNullType",
    value: function visitNullType(node) {
      _superPropGet(SPIRVPrimitiveVariableAnalyzer, "visit", this, 3)([this]);
    }
  }, {
    key: "visitGenericLiteralType",
    value: function visitGenericLiteralType(node) {
      node.type.visit(this);
    }
  }, {
    key: "visitNativeType",
    value: function visitNativeType(node) {
      this.result.push({
        name: this.nameComponents.join(""),
        id: this._currentId++,
        type: this.typeMap.get(node),
        location: this._currentLocation++
      });
    }
  }, {
    key: "visitEnumType",
    value: function visitEnumType(node) {
      _superPropGet(SPIRVPrimitiveVariableAnalyzer, "visit", this, 3)([this]);
    }
  }, {
    key: "visitPtrType",
    value: function visitPtrType(node) {
      // Intentionally blank
    }
  }, {
    key: "visitArrayRefType",
    value: function visitArrayRefType(node) {
      this.visitNativeType(program.intrinsics.uint32);
      this.visitNativeType(program.intrinsics.uint32);
    }
  }, {
    key: "visitArrayType",
    value: function visitArrayType(node) {
      for (var i = 0; i < node.numElements.value; ++i) {
        this.nameComponents.push("[");
        this.nameComponents.push(i.toString());
        this.nameComponents.push("]");
        node.elementType.visit(this);
        this.nameComponents.pop();
        this.nameComponents.pop();
        this.nameComponents.pop();
      }
    }
  }, {
    key: "visitStructType",
    value: function visitStructType(node) {
      var builtInStructs = ["struct vec2<> { int32 x; int32 y }", "struct vec2<> { uint32 x; uint32 y; }", "struct vec2<> { float32 x; float32 y; }", "struct vec2<> { float64 x; float64 y; }", "struct vec3<> { int32 x; int32 y; int32 z; }", "struct vec3<> { uint32 x; uint32 y; uint32 z; }", "struct vec3<> { float32 x; float32 y; float32 z; }", "struct vec3<> { float64 x; float64 y; float64 z; }", "struct vec4<> { int32 x; int32 y; int32 z; int32 w; }", "struct vec4<> { uint32 x; uint32 y; uint32 z; uint32 w; }", "struct vec4<> { float32 x; float32 y; float32 z; float32 w; }", "struct vec4<> { float64 x; float64 y; float64 z; float64 w; }"];
      for (var _i = 0, _builtInStructs = builtInStructs; _i < _builtInStructs.length; _i++) {
        var builtInStruct = _builtInStructs[_i];
        if (node.toString() == builtInStruct) {
          this.result.push({
            name: this.nameComponents.join(""),
            id: this._currentId++,
            type: this.typeMap.get(node.toString()).id,
            location: this._currentLocation++
          });
          return;
        }
      }
      var _iterator = _createForOfIteratorHelper(node.fields),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var field = _step.value;
          var dotPrefix = this.nameComponents.length > 0;
          if (dotPrefix) this.nameComponents.push(".");
          this.nameComponents.push(field.name);
          field.visit(this);
          this.nameComponents.pop();
          if (dotPrefix) this.nameComponents.pop();
        }
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
    }
  }]);
}(Visitor);