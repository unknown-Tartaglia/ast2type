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
function inferTypesForCall(func, typeArguments, argumentTypes, returnType) {
  if (typeArguments.length && typeArguments.length != func.typeParameters.length) return {
    failure: new OverloadResolutionFailure(func, "Wrong number of type arguments (passed " + typeArguments.length + ", require " + func.typeParameters.length + ")")
  };
  if (argumentTypes.length != func.parameters.length) return {
    failure: new OverloadResolutionFailure(func, "Wrong number of arguments (passed " + argumentTypes.length + ", require " + func.parameters.length + ")")
  };
  var unificationContext = new UnificationContext(func.typeParametersForCallResolution);
  for (var i = 0; i < typeArguments.length; ++i) {
    var argument = typeArguments[i];
    var parameter = func.typeParameters[i];
    if (!argument.unify(unificationContext, parameter)) return {
      failure: new OverloadResolutionFailure(func, "Type argument #" + (i + 1) + " for parameter " + parameter.name + " does not match (passed " + argument + ", require " + parameter + ")")
    };
  }
  for (var _i = 0; _i < argumentTypes.length; ++_i) {
    if (!argumentTypes[_i]) throw new Error("Null argument type at i = " + _i);
    if (!argumentTypes[_i].unify(unificationContext, func.parameters[_i].type)) return {
      failure: new OverloadResolutionFailure(func, "Argument #" + (_i + 1) + " " + (func.parameters[_i].name ? "for parameter " + func.parameters[_i].name + " " : "") + "does not match (passed " + argumentTypes[_i] + ", require " + func.parameters[_i].type + ")")
    };
  }
  if (returnType && !returnType.unify(unificationContext, func.returnType)) return {
    failure: new OverloadResolutionFailure(func, "Return type " + func.returnType + " does not match " + returnType)
  };
  var verificationResult = unificationContext.verify();
  if (!verificationResult.result) return {
    failure: new OverloadResolutionFailure(func, verificationResult.reason)
  };
  var shouldBuildTypeArguments = !typeArguments.length;
  if (shouldBuildTypeArguments) typeArguments = [];
  var _iterator = _createForOfIteratorHelper(func.typeParameters),
    _step;
  try {
    for (_iterator.s(); !(_step = _iterator.n()).done;) {
      var typeParameter = _step.value;
      var typeArgument = unificationContext.find(typeParameter);
      if (typeArgument == typeParameter) return {
        failure: new OverloadResolutionFailure(func, "Type parameter " + typeParameter + " did not get assigned a type")
      };
      if (shouldBuildTypeArguments) typeArguments.push(typeArgument);
    }
  } catch (err) {
    _iterator.e(err);
  } finally {
    _iterator.f();
  }
  return {
    func: func,
    unificationContext: unificationContext,
    typeArguments: typeArguments
  };
}