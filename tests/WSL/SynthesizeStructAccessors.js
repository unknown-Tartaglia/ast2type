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
function synthesizeStructAccessors(program) {
  var _iterator = _createForOfIteratorHelper(program.types.values()),
    _step;
  try {
    var _loop = function _loop() {
      var type = _step.value;
      if (!(type instanceof StructType)) return 1; // continue
      var _iterator2 = _createForOfIteratorHelper(type.fields),
        _step2;
      try {
        var _loop2 = function _loop2() {
          var field = _step2.value;
          function createTypeParameters() {
            return type.typeParameters.map(function (typeParameter) {
              return typeParameter.visit(new TypeParameterRewriter());
            });
          }
          function createTypeArguments() {
            return typeParameters.map(function (typeParameter) {
              return typeParameter.visit(new AutoWrapper());
            });
          }
          function setupImplementationData(nativeFunc, implementation) {
            nativeFunc.instantiateImplementation = function (substitution) {
              var newType = type.instantiate(nativeFunc.typeParameters.map(function (typeParameter) {
                var substitute = substitution.map.get(typeParameter);
                if (!substitute) throw new Error("Null substitute for type parameter " + typeParameter);
                return substitute;
              }));
              return {
                type: newType,
                fieldName: field.name
              };
            };
            nativeFunc.visitImplementationData = function (implementationData, visitor) {
              // Visiting the type first ensures that the struct layout builder figures out the field's
              // offset.
              implementationData.type.visit(visitor);
            };
            nativeFunc.didLayoutStructsInImplementationData = function (implementationData) {
              var structSize = implementationData.type.size;
              if (structSize == null) throw new Error("No struct size for " + nativeFunc);
              var field = implementationData.type.fieldByName(implementationData.fieldName);
              if (!field) throw new Error("Could not find field");
              var offset = field.offset;
              var fieldSize = field.type.size;
              if (fieldSize == null) throw new Error("No field size for " + nativeFunc);
              if (offset == null) throw new Error("No offset for " + nativeFunc);
              implementationData.offset = offset;
              implementationData.structSize = structSize;
              implementationData.fieldSize = fieldSize;
            };
            nativeFunc.implementation = function (argumentList, node) {
              var nativeFuncInstance = node.nativeFuncInstance;
              var implementationData = nativeFuncInstance.implementationData;
              return implementation(argumentList, implementationData.offset, implementationData.structSize, implementationData.fieldSize);
            };
          }
          function createFieldType() {
            return field.type.visit(new Substitution(type.typeParameters, typeParameters));
          }
          function createTypeRef() {
            return TypeRef.instantiate(type, createTypeArguments());
          }
          var isCast = false;
          var shaderType;
          var typeParameters;
          var nativeFunc;

          // The getter: operator.field
          typeParameters = createTypeParameters();
          nativeFunc = new NativeFunc(field.origin, "operator." + field.name, createFieldType(), typeParameters, [new FuncParameter(field.origin, null, createTypeRef())], isCast, shaderType);
          setupImplementationData(nativeFunc, function (_ref, offset, structSize, fieldSize) {
            var _ref2 = _slicedToArray(_ref, 1),
              base = _ref2[0];
            var result = new EPtr(new EBuffer(fieldSize), 0);
            result.copyFrom(base.plus(offset), fieldSize);
            return result;
          });
          program.add(nativeFunc);

          // The setter: operator.field=
          typeParameters = createTypeParameters();
          nativeFunc = new NativeFunc(field.origin, "operator." + field.name + "=", createTypeRef(), typeParameters, [new FuncParameter(field.origin, null, createTypeRef()), new FuncParameter(field.origin, null, createFieldType())], isCast, shaderType);
          setupImplementationData(nativeFunc, function (_ref3, offset, structSize, fieldSize) {
            var _ref4 = _slicedToArray(_ref3, 2),
              base = _ref4[0],
              value = _ref4[1];
            var result = new EPtr(new EBuffer(structSize), 0);
            result.copyFrom(base, structSize);
            result.plus(offset).copyFrom(value, fieldSize);
            return result;
          });
          program.add(nativeFunc);

          // The ander: operator&.field
          function setupAnder(addressSpace) {
            typeParameters = createTypeParameters();
            nativeFunc = new NativeFunc(field.origin, "operator&." + field.name, new PtrType(field.origin, addressSpace, createFieldType()), typeParameters, [new FuncParameter(field.origin, null, new PtrType(field.origin, addressSpace, createTypeRef()))], isCast, shaderType);
            setupImplementationData(nativeFunc, function (_ref5, offset, structSize, fieldSize) {
              var _ref6 = _slicedToArray(_ref5, 1),
                base = _ref6[0];
              base = base.loadValue();
              if (!base) throw new WTrapError(node.origin.originString, "Null dereference");
              return EPtr.box(base.plus(offset));
            });
            program.add(nativeFunc);
          }
          setupAnder("thread");
          setupAnder("threadgroup");
          setupAnder("device");
          setupAnder("constant");
        };
        for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
          _loop2();
        }
      } catch (err) {
        _iterator2.e(err);
      } finally {
        _iterator2.f();
      }
    };
    for (_iterator.s(); !(_step = _iterator.n()).done;) {
      if (_loop()) continue;
    }
  } catch (err) {
    _iterator.e(err);
  } finally {
    _iterator.f();
  }
}