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

function _slicedToArray(r, e) { return _arrayWithHoles(r) || _iterableToArrayLimit(r, e) || _unsupportedIterableToArray(r, e) || _nonIterableRest(); }
function _nonIterableRest() { throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); }
function _iterableToArrayLimit(r, l) { var t = null == r ? null : "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (null != t) { var e, n, i, u, a = [], f = !0, o = !1; try { if (i = (t = t.call(r)).next, 0 === l) { if (Object(t) !== t) return; f = !1; } else for (; !(f = (e = i.call(t)).done) && (a.push(e.value), a.length !== l); f = !0); } catch (r) { o = !0, n = r; } finally { try { if (!f && null != t.return && (u = t.return(), Object(u) !== u)) return; } finally { if (o) throw n; } } return a; } }
function _arrayWithHoles(r) { if (Array.isArray(r)) return r; }
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function synthesizeEnumFunctions(program) {
  var _iterator = _createForOfIteratorHelper(program.types.values()),
    _step;
  try {
    for (_iterator.s(); !(_step = _iterator.n()).done;) {
      var type = _step.value;
      if (!(type instanceof EnumType)) continue;
      var nativeFunc = void 0;
      var isCast = false;
      var shaderType = void 0;
      nativeFunc = new NativeFunc(type.origin, "operator==", new TypeRef(type.origin, "bool", []), [], [new FuncParameter(type.origin, null, new TypeRef(type.origin, type.name, [])), new FuncParameter(type.origin, null, new TypeRef(type.origin, type.name, []))], isCast, shaderType);
      nativeFunc.implementation = function (_ref) {
        var _ref2 = _slicedToArray(_ref, 2),
          left = _ref2[0],
          right = _ref2[1];
        return EPtr.box(left.loadValue() == right.loadValue());
      };
      program.add(nativeFunc);
      nativeFunc = new NativeFunc(type.origin, "operator.value", type.baseType.visit(new Rewriter()), [], [new FuncParameter(type.origin, null, new TypeRef(type.origin, type.name, []))], isCast, shaderType);
      nativeFunc.implementation = function (_ref3) {
        var _ref4 = _slicedToArray(_ref3, 1),
          value = _ref4[0];
        return value;
      };
      program.add(nativeFunc);
      nativeFunc = new NativeFunc(type.origin, "operator cast", type.baseType.visit(new Rewriter()), [], [new FuncParameter(type.origin, null, new TypeRef(type.origin, type.name, []))], isCast, shaderType);
      nativeFunc.implementation = function (_ref5) {
        var _ref6 = _slicedToArray(_ref5, 1),
          value = _ref6[0];
        return value;
      };
      program.add(nativeFunc);
      nativeFunc = new NativeFunc(type.origin, "operator cast", new TypeRef(type.origin, type.name, []), [], [new FuncParameter(type.origin, null, type.baseType.visit(new Rewriter()))], isCast, shaderType);
      nativeFunc.implementation = function (_ref7) {
        var _ref8 = _slicedToArray(_ref7, 1),
          value = _ref8[0];
        return value;
      };
      program.add(nativeFunc);
    }
  } catch (err) {
    _iterator.e(err);
  } finally {
    _iterator.f();
  }
}