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
var EPtr = /*#__PURE__*/function () {
  function EPtr(buffer, offset) {
    _classCallCheck(this, EPtr);
    if (offset == null || offset != offset) throw new Error("Bad offset: " + offset);
    this._buffer = buffer;
    this._offset = offset;
  }

  // The interpreter always passes around pointers to things. This means that sometimes we will
  // want to return a value but we have to "invent" a pointer to that value. No problem, this
  // function is here to help.
  //
  // In a real execution environment, uses of this manifest as SSA temporaries.
  return _createClass(EPtr, [{
    key: "box",
    value: function box(value) {
      this._buffer.set(0, value);
      return this;
    }
  }, {
    key: "buffer",
    get: function get() {
      return this._buffer;
    }
  }, {
    key: "offset",
    get: function get() {
      return this._offset;
    }
  }, {
    key: "plus",
    value: function plus(offset) {
      return new EPtr(this.buffer, this.offset + offset);
    }
  }, {
    key: "loadValue",
    value: function loadValue() {
      return this.buffer.get(this.offset);
    }
  }, {
    key: "get",
    value: function get(offset) {
      return this.buffer.get(this.offset + offset);
    }
  }, {
    key: "set",
    value: function set(offset, value) {
      this.buffer.set(this.offset + offset, value);
    }
  }, {
    key: "copyFrom",
    value: function copyFrom(other, size) {
      if (size == null) throw new Error("Cannot copy null size");
      for (var i = size; i--;) this.set(i, other.get(i));
    }
  }, {
    key: "toString",
    value: function toString() {
      return "B" + this.buffer.index + ":" + this.offset;
    }
  }], [{
    key: "box",
    value: function box(value) {
      return new EPtr(new EBuffer(1), 0).box(value);
    }
  }]);
}();