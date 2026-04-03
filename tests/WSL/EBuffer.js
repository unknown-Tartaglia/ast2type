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
var eBufferCount = 0;
var canAllocateEBuffers = true;
var EBuffer = /*#__PURE__*/function () {
  function EBuffer(size) {
    _classCallCheck(this, EBuffer);
    if (!canAllocateEBuffers) throw new Error("Trying to allocate EBuffer while allocation is disallowed");
    this._index = eBufferCount++;
    this._array = new Array(size);
  }
  return _createClass(EBuffer, [{
    key: "get",
    value: function get(index) {
      if (index < 0 || index >= this._array.length) throw new Error("Out of bounds buffer access (buffer = " + this + ", index = " + index + ")");
      return this._array[index];
    }
  }, {
    key: "set",
    value: function set(index, value) {
      if (index < 0 || index >= this._array.length) throw new Error("out of bounds buffer access (buffer = " + this + ", index = " + index + ")");
      this._array[index] = value;
    }
  }, {
    key: "index",
    get: function get() {
      return this._index;
    }
  }, {
    key: "toString",
    value: function toString() {
      return "B" + this._index + ":[" + this._array + "]";
    }
  }], [{
    key: "setCanAllocateEBuffers",
    value: function setCanAllocateEBuffers(value, callback) {
      var oldCanAllocateEBuffers = canAllocateEBuffers;
      canAllocateEBuffers = value;
      try {
        return callback();
      } finally {
        canAllocateEBuffers = oldCanAllocateEBuffers;
      }
    }
  }, {
    key: "disallowAllocation",
    value: function disallowAllocation(callback) {
      return EBuffer.setCanAllocateEBuffers(false, callback);
    }
  }, {
    key: "allowAllocation",
    value: function allowAllocation(callback) {
      return EBuffer.setCanAllocateEBuffers(true, callback);
    }
  }]);
}();