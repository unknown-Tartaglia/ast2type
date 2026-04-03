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
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
var Lexer = /*#__PURE__*/function () {
  function Lexer(origin, originKind, lineNumberOffset, text) {
    _classCallCheck(this, Lexer);
    if (!isOriginKind(originKind)) throw new Error("Bad origin kind: " + originKind);
    this._origin = origin;
    this._originKind = originKind;
    this._lineNumberOffset = lineNumberOffset;
    this._text = text;
    this._index = 0;
    this._stack = [];
  }
  return _createClass(Lexer, [{
    key: "lineNumber",
    get: function get() {
      return this.lineNumberForIndex(this._index);
    }
  }, {
    key: "origin",
    get: function get() {
      return this._origin;
    }
  }, {
    key: "originString",
    get: function get() {
      return this._origin + ":" + (this.lineNumber + 1);
    }
  }, {
    key: "originKind",
    get: function get() {
      return this._originKind;
    }
  }, {
    key: "lineNumberForIndex",
    value: function lineNumberForIndex(index) {
      var matches = this._text.substring(0, index).match(/\n/g);
      return (matches ? matches.length : 0) + this._lineNumberOffset;
    }
  }, {
    key: "state",
    get: function get() {
      return {
        index: this._index,
        stack: this._stack.concat()
      };
    },
    set: function set(value) {
      this._index = value.index;
      this._stack = value.stack;
    }
  }, {
    key: "next",
    value: function next() {
      var _this = this;
      if (this._stack.length) return this._stack.pop();
      if (this._index >= this._text.length) return null;
      var isCCommentBegin = /\/\*/;
      var isCPlusPlusCommentBegin = /\/\//;
      var result = function result(kind) {
        var text = RegExp.lastMatch;
        var token = new LexerToken(_this, _this._index, kind, text);
        _this._index += text.length;
        return token;
      };
      var relevantText;
      for (;;) {
        relevantText = this._text.substring(this._index);
        if (/^\s+/.test(relevantText)) {
          this._index += RegExp.lastMatch.length;
          continue;
        }
        if (/^\/\*/.test(relevantText)) {
          var endIndex = relevantText.search(/\*\//);
          if (endIndex < 0) this.fail("Unterminated comment");
          this._index += endIndex;
          continue;
        }
        if (/^\/\/.*/.test(relevantText)) {
          this._index += RegExp.lastMatch.length;
          continue;
        }
        break;
      }
      if (this._index >= this._text.length) return null;

      // FIXME: Make this handle exp-form literals like 1e1.
      if (/^(([0-9]*\.[0-9]+[fd]?)|([0-9]+\.[0-9]*[fd]?))/.test(relevantText)) return result("floatLiteral");

      // FIXME: Make this do Unicode.
      if (Lexer._textIsIdentifierImpl(relevantText)) {
        if (/^(struct|protocol|typedef|if|else|enum|continue|break|switch|case|default|for|while|do|return|constant|device|threadgroup|thread|operator|null|true|false)$/.test(RegExp.lastMatch)) return result("keyword");
        if (this._originKind == "native" && /^(native|restricted)$/.test(RegExp.lastMatch)) return result("keyword");
        return result("identifier");
      }
      if (/^0x[0-9a-fA-F]+u/.test(relevantText)) return result("uintHexLiteral");
      if (/^0x[0-9a-fA-F]+/.test(relevantText)) return result("intHexLiteral");
      if (/^[0-9]+u/.test(relevantText)) return result("uintLiteral");
      if (/^[0-9]+/.test(relevantText)) return result("intLiteral");
      if (/^<<|>>|->|>=|<=|==|!=|\+=|-=|\*=|\/=|%=|\^=|\|=|&=|\+\+|--|&&|\|\||([{}()\[\]?:=+*\/,.%!~^&|<>@;-])/.test(relevantText)) return result("punctuation");
      var remaining = relevantText.substring(0, 20).split(/\s/)[0];
      if (!remaining.length) remaining = relevantText.substring(0, 20);
      this.fail("Unrecognized token beginning with: " + remaining);
    }
  }, {
    key: "push",
    value: function push(token) {
      this._stack.push(token);
    }
  }, {
    key: "peek",
    value: function peek() {
      var result = this.next();
      this.push(result);
      return result;
    }
  }, {
    key: "fail",
    value: function fail(error) {
      throw new WSyntaxError(this.originString, error);
    }
  }, {
    key: "backtrackingScope",
    value: function backtrackingScope(callback) {
      var state = this.state;
      try {
        return callback();
      } catch (e) {
        if (e instanceof WSyntaxError) {
          this.state = state;
          return null;
        }
        throw e;
      }
    }
  }, {
    key: "testScope",
    value: function testScope(callback) {
      var state = this.state;
      try {
        callback();
        return true;
      } catch (e) {
        if (e instanceof WSyntaxError) return false;
        throw e;
      } finally {
        this.state = state;
      }
    }
  }], [{
    key: "_textIsIdentifierImpl",
    value: function _textIsIdentifierImpl(text) {
      return /^[^\d\W]\w*/.test(text);
    }
  }, {
    key: "textIsIdentifier",
    value: function textIsIdentifier(text) {
      return Lexer._textIsIdentifierImpl(text) && !RegExp.rightContext.length;
    }
  }]);
}();