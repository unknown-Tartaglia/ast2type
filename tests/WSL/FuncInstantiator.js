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
function _superPropGet(t, o, e, r) { var p = _get(_getPrototypeOf(1 & r ? t.prototype : t), o, e); return 2 & r && "function" == typeof p ? function (t) { return p.apply(e, t); } : p; }
function _get() { return _get = "undefined" != typeof Reflect && Reflect.get ? Reflect.get.bind() : function (e, t, r) { var p = _superPropBase(e, t); if (p) { var n = Object.getOwnPropertyDescriptor(p, t); return n.get ? n.get.call(arguments.length < 3 ? e : r) : n.value; } }, _get.apply(null, arguments); }
function _superPropBase(t, o) { for (; !{}.hasOwnProperty.call(t, o) && null !== (t = _getPrototypeOf(t));); return t; }
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function _callSuper(t, o, e) { return o = _getPrototypeOf(o), _possibleConstructorReturn(t, _isNativeReflectConstruct() ? Reflect.construct(o, e || [], _getPrototypeOf(t).constructor) : o.apply(t, e)); }
function _possibleConstructorReturn(t, e) { if (e && ("object" == _typeof(e) || "function" == typeof e)) return e; if (void 0 !== e) throw new TypeError("Derived constructors may only return object or undefined"); return _assertThisInitialized(t); }
function _assertThisInitialized(e) { if (void 0 === e) throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); return e; }
function _isNativeReflectConstruct() { try { var t = !Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], function () {})); } catch (t) {} return (_isNativeReflectConstruct = function _isNativeReflectConstruct() { return !!t; })(); }
function _getPrototypeOf(t) { return _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf.bind() : function (t) { return t.__proto__ || Object.getPrototypeOf(t); }, _getPrototypeOf(t); }
function _inherits(t, e) { if ("function" != typeof e && null !== e) throw new TypeError("Super expression must either be null or a function"); t.prototype = Object.create(e && e.prototype, { constructor: { value: t, writable: !0, configurable: !0 } }), Object.defineProperty(t, "prototype", { writable: !1 }), e && _setPrototypeOf(t, e); }
function _setPrototypeOf(t, e) { return _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function (t, e) { return t.__proto__ = e, t; }, _setPrototypeOf(t, e); }
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
var FuncInstantiator = /*#__PURE__*/function () {
  function FuncInstantiator(program) {
    _classCallCheck(this, FuncInstantiator);
    this._program = program;
    this._instances = new Map();
  }

  // Returns a Func object that uniquely identifies a particular system of type arguments. You must
  // intantiate things with concrete types, because this code casually assumes this. Note that this
  // will return a different func from `func` no matter what. This ensures that we can use the
  // returned func for rewrites that instantiate types without destroying our ability to do overload
  // resolutions on the original Program.
  return _createClass(FuncInstantiator, [{
    key: "getUnique",
    value: function getUnique(func, typeArguments) {
      var FindTypeVariable = /*#__PURE__*/function (_Visitor) {
        function FindTypeVariable() {
          _classCallCheck(this, FindTypeVariable);
          return _callSuper(this, FindTypeVariable, arguments);
        }
        _inherits(FindTypeVariable, _Visitor);
        return _createClass(FindTypeVariable, [{
          key: "visitTypeRef",
          value: function visitTypeRef(node) {
            var _iterator = _createForOfIteratorHelper(node.typeArguments),
              _step;
            try {
              for (_iterator.s(); !(_step = _iterator.n()).done;) {
                var typeArgument = _step.value;
                typeArgument.visit(this);
              }
            } catch (err) {
              _iterator.e(err);
            } finally {
              _iterator.f();
            }
          }
        }, {
          key: "visitTypeVariable",
          value: function visitTypeVariable(node) {
            throw new Error("Unexpected type variable: " + node + " when instantiating " + func + " with arguments " + typeArguments);
          }
        }]);
      }(Visitor);
      var _iterator2 = _createForOfIteratorHelper(typeArguments),
        _step2;
      try {
        for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
          var typeArgument = _step2.value;
          typeArgument.visit(new FindTypeVariable());
        }
      } catch (err) {
        _iterator2.e(err);
      } finally {
        _iterator2.f();
      }
      var instances = this._instances.get(func);
      if (!instances) this._instances.set(func, instances = []);
      var _iterator3 = _createForOfIteratorHelper(instances),
        _step3;
      try {
        for (_iterator3.s(); !(_step3 = _iterator3.n()).done;) {
          var _instance = _step3.value;
          var ok = true;
          for (var i = _instance.typeArguments.length; i--;) {
            if (!_instance.typeArguments[i].equals(typeArguments[i])) {
              ok = false;
              break;
            }
          }
          if (!ok) continue;
          return _instance.func;
        }
      } catch (err) {
        _iterator3.e(err);
      } finally {
        _iterator3.f();
      }
      var thisInstantiator = this;
      var InstantiationSubstitution = /*#__PURE__*/function (_Substitution) {
        function InstantiationSubstitution() {
          _classCallCheck(this, InstantiationSubstitution);
          return _callSuper(this, InstantiationSubstitution, arguments);
        }
        _inherits(InstantiationSubstitution, _Substitution);
        return _createClass(InstantiationSubstitution, [{
          key: "visitCallExpression",
          value: function visitCallExpression(node) {
            var result = _superPropGet(InstantiationSubstitution, "visitCallExpression", this, 3)([node]);

            // We may have to re-resolve the function call, if it was a call to a protocol
            // signature.
            if (result.func instanceof ProtocolFuncDecl) {
              var overload = resolveOverloadImpl(result.possibleOverloads, result.typeArguments, result.argumentTypes, result.returnType);
              if (!overload.func) throw new Error("Could not resolve protocol signature function call during instantiation: " + result.func + (overload.failures.length ? "; tried:\n" + overload.failures.join("\n") : ""));
              result.resolveToOverload(overload);
            }
            if (result.func.isNative) result.nativeFuncInstance = thisInstantiator.getUnique(result.func, result.actualTypeArguments);
            return result;
          }
        }]);
      }(Substitution);
      var substitution = new InstantiationSubstitution(func.typeParameters, typeArguments);
      var InstantiationInstantiateImmediates = /*#__PURE__*/function (_InstantiateImmediate) {
        function InstantiationInstantiateImmediates() {
          _classCallCheck(this, InstantiationInstantiateImmediates);
          return _callSuper(this, InstantiationInstantiateImmediates, arguments);
        }
        _inherits(InstantiationInstantiateImmediates, _InstantiateImmediate);
        return _createClass(InstantiationInstantiateImmediates, [{
          key: "visitCallExpression",
          value: function visitCallExpression(node) {
            var _this = this;
            // We need to preserve certain things that would have instantiated, but that we cannot
            // instantiate without breaking chain-instantiations (generic function calls generic
            // function so therefore the instantiated generic function must still have the original
            // (uninstantiated) types to instantiate the generic function that it calls).
            var result = new CallExpression(node.origin, node.name, node.typeArguments, node.argumentList.map(function (argument) {
              return Node.visit(argument, _this);
            }));
            result = this.processDerivedCallData(node, result);
            result.argumentTypes = Array.from(node.argumentTypes);
            if (node.isCast) result.setCastData(node.returnType);
            result.actualTypeArguments = Array.from(node.actualTypeArguments);
            return result;
          }
        }]);
      }(InstantiateImmediates);
      var instantiateImmediates = new InstantiationInstantiateImmediates();
      var Instantiate = /*#__PURE__*/function () {
        function Instantiate() {
          _classCallCheck(this, Instantiate);
        }
        return _createClass(Instantiate, [{
          key: "visitFuncDef",
          value: function visitFuncDef(func) {
            var returnType = func.returnType.visit(substitution);
            returnType = returnType.visit(instantiateImmediates);
            var parameters = func.parameters.map(function (parameter) {
              return parameter.visit(substitution);
            });
            parameters = parameters.map(function (parameter) {
              return parameter.visit(instantiateImmediates);
            });
            var body = func.body.visit(substitution);
            body = body.visit(instantiateImmediates);
            return new FuncDef(func.origin, func.name, returnType, [], parameters, body, func.isCast, func.shaderType);
          }
        }, {
          key: "visitNativeFunc",
          value: function visitNativeFunc(func) {
            return new NativeFuncInstance(func, func.returnType.visit(substitution).visit(instantiateImmediates), func.parameters.map(function (parameter) {
              return parameter.visit(substitution).visit(instantiateImmediates);
            }), func.isCast, func.shaderType, func.instantiateImplementation(substitution));
          }
        }]);
      }();
      var resultingFunc = func.visit(new Instantiate());
      resultingFunc.uninstantiatedReturnType = func.returnType.visit(substitution);
      var instance = {
        func: resultingFunc,
        typeArguments: typeArguments
      };
      instances.push(instance);
      return resultingFunc;
    }
  }]);
}();