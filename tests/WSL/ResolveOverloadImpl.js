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

function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function resolveOverloadImpl(functions, typeArguments, argumentTypes, returnType) {
  var allowEntryPoint = arguments.length > 4 && arguments[4] !== undefined ? arguments[4] : false;
  if (!functions) throw new Error("Null functions; that should have been caught by the caller.");
  var failures = [];
  var successes = [];
  var _iterator = _createForOfIteratorHelper(functions),
    _step;
  try {
    for (_iterator.s(); !(_step = _iterator.n()).done;) {
      var func = _step.value;
      if (!allowEntryPoint && func.shaderType) {
        failures.push(new OverloadResolutionFailure(func, "Function is a " + func.shaderType + " shader, so it cannot be called from within an existing shader."));
        continue;
      }
      var _overload = inferTypesForCall(func, typeArguments, argumentTypes, returnType);
      if (_overload.failure) failures.push(_overload.failure);else successes.push(_overload);
    }
  } catch (err) {
    _iterator.e(err);
  } finally {
    _iterator.f();
  }
  if (!successes.length) return {
    failures: failures
  };
  var minimumConversionCost = successes.reduce(function (result, overload) {
    return Math.min(result, overload.unificationContext.conversionCost);
  }, Infinity);
  successes = successes.filter(function (overload) {
    return overload.unificationContext.conversionCost == minimumConversionCost;
  });

  // If any of the signatures are restricted then we consider those first. This is an escape mechanism for
  // built-in things.
  // FIXME: It should be an error to declare a function that is at least as specific as a restricted function.
  // https://bugs.webkit.org/show_bug.cgi?id=176580
  var hasRestricted = successes.reduce(function (result, overload) {
    return result || overload.func.isRestricted;
  }, false);
  if (hasRestricted) successes = successes.filter(function (overload) {
    return overload.func.isRestricted;
  });

  // We are only interested in functions that are at least as specific as all of the others. This means
  // that they can be "turned around" and applied onto all of the other functions in the list.
  var prunedSuccesses = [];
  for (var i = 0; i < successes.length; ++i) {
    var ok = true;
    var argumentFunc = successes[i].func;
    for (var j = 0; j < successes.length; ++j) {
      if (i == j) continue;
      var parameterFunc = successes[j].func;
      var overload = inferTypesForCall(parameterFunc, typeArguments.length ? argumentFunc.typeParameters : [], argumentFunc.parameterTypes, argumentFunc.returnTypeForOverloadResolution);
      if (!overload.func) {
        ok = false;
        break;
      }
    }
    if (ok) prunedSuccesses.push(successes[i]);
  }
  if (prunedSuccesses.length == 1) return prunedSuccesses[0];
  var ambiguityList;
  var message;
  if (prunedSuccesses.length == 0) {
    ambiguityList = successes;
    message = "Ambiguous overload - no function can be applied to all others";
  } else {
    ambiguityList = prunedSuccesses;
    message = "Ambiguous overload - functions mutually applicable";
  }
  return {
    failures: ambiguityList.map(function (overload) {
      return new OverloadResolutionFailure(overload.func, message);
    })
  };
}