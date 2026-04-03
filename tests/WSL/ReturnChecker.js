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
var ReturnChecker = /*#__PURE__*/function (_Visitor) {
  function ReturnChecker(program) {
    var _this;
    _classCallCheck(this, ReturnChecker);
    _this = _callSuper(this, ReturnChecker);
    _this.returnStyle = {
      DefinitelyReturns: "Definitely Returns",
      DefinitelyDoesntReturn: "Definitely Doesn't Return",
      HasntReturnedYet: "Hasn't Returned Yet"
    };
    _this._program = program;
    return _this;
  }
  _inherits(ReturnChecker, _Visitor);
  return _createClass(ReturnChecker, [{
    key: "_mergeReturnStyle",
    value: function _mergeReturnStyle(a, b) {
      if (!a) return b;
      if (!b) return a;
      switch (a) {
        case this.returnStyle.DefinitelyReturns:
        case this.returnStyle.DefinitelyDoesntReturn:
          if (a == b) return a;
          return this.returnStyle.HasntReturnedYet;
        case this.returnStyle.HasntReturnedYet:
          return this.returnStyle.HasntReturnedYet;
        default:
          throw new Error("Bad return style: " + a);
      }
    }
  }, {
    key: "visitFuncDef",
    value: function visitFuncDef(node) {
      if (node.returnType.equals(node.program.intrinsics.void)) return;
      var bodyValue = node.body.visit(this);
      if (bodyValue == this.returnStyle.DefinitelyDoesntReturn || bodyValue == this.returnStyle.HasntReturnedYet) throw new WTypeError(node.origin.originString, "Function does not return");
    }
  }, {
    key: "visitBlock",
    value: function visitBlock(node) {
      var _iterator = _createForOfIteratorHelper(node.statements),
        _step;
      try {
        for (_iterator.s(); !(_step = _iterator.n()).done;) {
          var statement = _step.value;
          switch (statement.visit(this)) {
            case this.returnStyle.DefinitelyReturns:
              return this.returnStyle.DefinitelyReturns;
            case this.returnStyle.DefinitelyDoesntReturn:
              return this.returnStyle.DefinitelyDoesntReturn;
            case this.returnStyle.HasntReturnedYet:
              continue;
          }
        }
      } catch (err) {
        _iterator.e(err);
      } finally {
        _iterator.f();
      }
      return this.returnStyle.HasntReturnedYet;
    }
  }, {
    key: "visitIfStatement",
    value: function visitIfStatement(node) {
      if (node.elseBody) {
        var bodyValue = node.body.visit(this);
        var elseValue = node.elseBody.visit(this);
        return this._mergeReturnStyle(bodyValue, elseValue);
      }
      return this.returnStyle.HasntReturnedYet;
    }
  }, {
    key: "_isBoolCastFromLiteralTrue",
    value: function _isBoolCastFromLiteralTrue(node) {
      return node.isCast && node.returnType instanceof TypeRef && node.returnType.equals(this._program.intrinsics.bool) && node.argumentList.length == 1 && node.argumentList[0] instanceof BoolLiteral && node.argumentList[0].value;
    }
  }, {
    key: "visitWhileLoop",
    value: function visitWhileLoop(node) {
      var bodyReturn = node.body.visit(this);
      if (node.conditional instanceof CallExpression && this._isBoolCastFromLiteralTrue(node.conditional)) {
        switch (bodyReturn) {
          case this.returnStyle.DefinitelyReturns:
            return this.returnStyle.DefinitelyReturns;
          case this.returnStyle.DefinitelyDoesntReturn:
          case this.returnStyle.HasntReturnedYet:
            return this.returnStyle.HasntReturnedYet;
        }
      }
      return this.returnStyle.HasntReturnedYet;
    }
  }, {
    key: "visitDoWhileLoop",
    value: function visitDoWhileLoop(node) {
      var result = this.returnStyle.HasntReturnedYet;
      switch (node.body.visit(this)) {
        case this.returnStyle.DefinitelyReturns:
          result = this.returnStyle.DefinitelyReturns;
        case this.returnStyle.DefinitelyDoesntReturn:
        case this.returnStyle.HasntReturnedYet:
          result = this.returnStyle.HasntReturnedYet;
      }
      return result;
    }
  }, {
    key: "visitForLoop",
    value: function visitForLoop(node) {
      var bodyReturn = node.body.visit(this);
      if (node.condition === undefined || this._isBoolCastFromLiteralTrue(node.condition)) {
        switch (bodyReturn) {
          case this.returnStyle.DefinitelyReturns:
            return this.returnStyle.DefinitelyReturns;
          case this.returnStyle.DefinitelyDoesntReturn:
          case this.returnStyle.HasntReturnedYet:
            return this.returnStyle.HasntReturnedYet;
        }
      }
    }
  }, {
    key: "visitSwitchStatement",
    value: function visitSwitchStatement(node) {
      // FIXME: This seems like it's missing things. For example, we need to be smart about this:
      //
      // for (;;) {
      //     switch (...) {
      //     ...
      //         continue; // This continues the for loop
      //     }
      // }
      //
      // I'm not sure what that means for this analysis. I'm starting to think that the right way to
      // build this analysis is to run a visitor that builds a CFG and then analyze the CFG.
      // https://bugs.webkit.org/show_bug.cgi?id=177172

      var returnStyle = null;
      var _iterator2 = _createForOfIteratorHelper(node.switchCases),
        _step2;
      try {
        for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
          var switchCase = _step2.value;
          var bodyStyle = switchCase.body.visit(this);
          // FIXME: The fact that we need this demonstrates the need for CFG analysis.
          if (bodyStyle == this.returnStyle.DefinitelyDoesntReturn) bodyStyle = this.returnStyle.HasntReturnedYet;
          returnStyle = this._mergeReturnStyle(returnStyle, bodyStyle);
        }
      } catch (err) {
        _iterator2.e(err);
      } finally {
        _iterator2.f();
      }
      return returnStyle;
    }
  }, {
    key: "visitReturn",
    value: function visitReturn(node) {
      return this.returnStyle.DefinitelyReturns;
    }
  }, {
    key: "visitTrapStatement",
    value: function visitTrapStatement(node) {
      return this.returnStyle.DefinitelyReturns;
    }
  }, {
    key: "visitBreak",
    value: function visitBreak(node) {
      return this.returnStyle.DefinitelyDoesntReturn;
    }
  }, {
    key: "visitContinue",
    value: function visitContinue(node) {
      // FIXME: This seems wrong. Consider a loop like:
      //
      // int foo() { for (;;) { continue; } }
      //
      // This program shouldn't claim that the problem is that it doesn't return.
      // https://bugs.webkit.org/show_bug.cgi?id=177172
      return this.returnStyle.DefinitelyDoesntReturn;
    }
  }]);
}(Visitor);