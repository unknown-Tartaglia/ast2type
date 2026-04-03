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

// This function accepts a JSON object describing the SPIR-V syntax.
// For example, https://github.com/KhronosGroup/SPIRV-Headers/blob/master/include/spirv/1.2/spirv.core.grammar.json
function _typeof(o) { "@babel/helpers - typeof"; return _typeof = "function" == typeof Symbol && "symbol" == typeof Symbol.iterator ? function (o) { return typeof o; } : function (o) { return o && "function" == typeof Symbol && o.constructor === Symbol && o !== Symbol.prototype ? "symbol" : typeof o; }, _typeof(o); }
function _classCallCheck(a, n) { if (!(a instanceof n)) throw new TypeError("Cannot call a class as a function"); }
function _defineProperties(e, r) { for (var t = 0; t < r.length; t++) { var o = r[t]; o.enumerable = o.enumerable || !1, o.configurable = !0, "value" in o && (o.writable = !0), Object.defineProperty(e, _toPropertyKey(o.key), o); } }
function _createClass(e, r, t) { return r && _defineProperties(e.prototype, r), t && _defineProperties(e, t), Object.defineProperty(e, "prototype", { writable: !1 }), e; }
function _toPropertyKey(t) { var i = _toPrimitive(t, "string"); return "symbol" == _typeof(i) ? i : i + ""; }
function _toPrimitive(t, r) { if ("object" != _typeof(t) || !t) return t; var e = t[Symbol.toPrimitive]; if (void 0 !== e) { var i = e.call(t, r || "default"); if ("object" != _typeof(i)) return i; throw new TypeError("@@toPrimitive must return a primitive value."); } return ("string" === r ? String : Number)(t); }
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function SPIRV(json) {
  var result = {
    ops: {},
    kinds: {}
  };
  var composites = new Map();
  var ids = new Map();
  var _iterator = _createForOfIteratorHelper(json.operand_kinds),
    _step;
  try {
    for (_iterator.s(); !(_step = _iterator.n()).done;) {
      var kind = _step.value;
      switch (kind.category) {
        case "BitEnum":
        case "ValueEnum":
          var enumerants = {
            category: kind.category
          };
          var _iterator6 = _createForOfIteratorHelper(kind.enumerants),
            _step6;
          try {
            for (_iterator6.s(); !(_step6 = _iterator6.n()).done;) {
              var enumerant = _step6.value;
              enumerants[enumerant.enumerant] = enumerant;
            }
          } catch (err) {
            _iterator6.e(err);
          } finally {
            _iterator6.f();
          }
          result.kinds[kind.kind] = enumerants;
          break;
        case "Composite":
          composites.set(kind.kind, kind);
          break;
        case "Id":
          ids.set(kind.kind, kind);
          break;
      }
    }
  } catch (err) {
    _iterator.e(err);
  } finally {
    _iterator.f();
  }
  function matchType(operandInfoKind, operand) {
    switch (operandInfoKind) {
      // FIXME: I'm not actually sure that Ids should be unsigned.
      case "IdResultType":
      case "IdResult":
      case "IdRef":
      case "IdScope":
      case "IdMemorySemantics":
      case "LiteralExtInstInteger":
        if (typeof operand != "number") throw new Error("Operand needs to be a number");
        if (operand >>> 0 != operand) throw new Error("Operand needs to fit in an unsigned int");
        return;
      case "LiteralInteger":
        if (typeof operand != "number") throw new Error("Operand needs to be a number");
        if ((operand | 0) != operand) throw new Error("Operand needs to fit in an int");
        return;
      case "LiteralString":
        if (typeof operand != "string") throw new Error("Operand needs to be a string");
        return;
      case "LiteralContextDependentNumber":
      case "LiteralSpecConstantOpInteger":
        if (typeof operand != "number") throw new Error("Operand needs to be a number");
        if (operand >>> 0 != operand && (operand | 0) != operand) throw new Error("Operand needs to fit in an unsigned int or an int.");
        return;
    }
    var kind = result.kinds[operandInfoKind];
    if (kind) {
      if (operand instanceof Array) {
        if (kind.category != "BitEnum") throw new Error("Passing an array to a " + kind.category + " operand");
        var _iterator2 = _createForOfIteratorHelper(operand),
          _step2;
        try {
          for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
            var operandItem = _step2.value;
            if (kind[operandItem.enumerant] != operandItem) throw new Error("" + operandItem.enumerant + " is not a member of " + operandInfoKind);
          }
        } catch (err) {
          _iterator2.e(err);
        } finally {
          _iterator2.f();
        }
        return;
      }
      if (kind[operand.enumerant] != operand) throw new Error("" + operand.enumerant + " is not a member of " + operandInfoKind);
      return;
    }
    throw new Error("Unknown type: " + operandInfoKind);
  }
  var OperandChecker = /*#__PURE__*/function () {
    function OperandChecker(operandInfos) {
      _classCallCheck(this, OperandChecker);
      this._operandInfos = operandInfos || [];
      this._operandIndex = 0;
      this._operandInfoIndex = 0;
      this._parameters = [];
    }
    return _createClass(OperandChecker, [{
      key: "_isStar",
      value: function _isStar(operandInfo) {
        switch (operandInfo.kind) {
          case "LiteralContextDependentNumber":
          case "LiteralSpecConstantOpInteger":
            // These types can be any width.
            return true;
        }
        return operandInfo.quantifier && operandInfo.quantifier == "*";
      }
    }, {
      key: "nextComparisonType",
      value: function (_nextComparisonType) {
        function nextComparisonType(_x) {
          return _nextComparisonType.apply(this, arguments);
        }
        nextComparisonType.toString = function () {
          return _nextComparisonType.toString();
        };
        return nextComparisonType;
      }(function (operand) {
        if (this._operandInfoIndex >= this._operandInfos.length) throw new Error("Specified operand does not correspond to any that the instruction expects.");
        var operandInfo = this._operandInfos[this._operandInfoIndex];
        var isStar = this._isStar(operandInfo);
        if (this._parameters.length != 0) {
          var _result = this._parameters[0];
          this._parameters.splice(0, 1);
          // FIXME: Handle parameters that require their own parameters
          ++this._operandIndex;
          if (this._parameters.length == 0 && !isStar) ++this._operandInfoIndex;
          return _result;
        }
        var composite = composites.get(operandInfo.kind);
        if (composite) {
          var _iterator3 = _createForOfIteratorHelper(composite.bases),
            _step3;
          try {
            for (_iterator3.s(); !(_step3 = _iterator3.n()).done;) {
              var base = _step3.value;
              this._parameters.push(base);
            }
          } catch (err) {
            _iterator3.e(err);
          } finally {
            _iterator3.f();
          }
          nextComparisonType(operand);
          return;
        }
        var kind = result.kinds[operandInfo.kind];
        if (kind) {
          var enumerant = kind[operand.enumerant];
          if (enumerant) {
            var parameters = enumerant.parameters;
            if (parameters) {
              var _iterator4 = _createForOfIteratorHelper(parameters),
                _step4;
              try {
                for (_iterator4.s(); !(_step4 = _iterator4.n()).done;) {
                  var parameter = _step4.value;
                  this._parameters.push(parameter.kind);
                }
              } catch (err) {
                _iterator4.e(err);
              } finally {
                _iterator4.f();
              }
              ++this._operandIndex;
              return operandInfo.kind;
            }
          }
        }
        ++this._operandIndex;
        if (!isStar) ++this._operandInfoIndex;
        return operandInfo.kind;
      })
    }, {
      key: "check",
      value: function check(operand) {
        matchType(this.nextComparisonType(operand), operand);
      }
    }, {
      key: "finalize",
      value: function finalize() {
        if (this._parameters.length != 0) throw new Error("Operand not specified for parameter.");
        for (var i = this._operandInfoIndex; i < this._operandInfos.length; ++i) {
          var operandInfo = this._operandInfos[i];
          var quantifier = operandInfo.quantifier;
          if (quantifier != "?" && !this._isStar(operandInfo)) throw new Error("Did not specify operand " + i + " to instruction.");
        }
      }
    }]);
  }();
  var _iterator5 = _createForOfIteratorHelper(json.instructions),
    _step5;
  try {
    var _loop = function _loop() {
      var instruction = _step5.value;
      if (!instruction.opname.startsWith("Op")) return 1; // continue
      var attributeName = instruction.opname.substring(2);
      result.ops[attributeName] = /*#__PURE__*/function () {
        function _class() {
          _classCallCheck(this, _class);
          var operandChecker = new OperandChecker(instruction.operands);
          for (var _len = arguments.length, operands = new Array(_len), _key = 0; _key < _len; _key++) {
            operands[_key] = arguments[_key];
          }
          for (var _i = 0, _operands = operands; _i < _operands.length; _i++) {
            var operand = _operands[_i];
            operandChecker.check(operand);
          }
          operandChecker.finalize();
          this._operands = operands;
        }
        return _createClass(_class, [{
          key: "operands",
          get: function get() {
            return this._operands;
          }
        }, {
          key: "opname",
          get: function get() {
            return instruction.opname;
          }
        }, {
          key: "opcode",
          get: function get() {
            return instruction.opcode;
          }
        }, {
          key: "operandInfo",
          get: function get() {
            return instruction.operands;
          }
        }, {
          key: "storageSize",
          get: function get() {
            var result = 1;
            var _iterator7 = _createForOfIteratorHelper(this.operands),
              _step7;
            try {
              for (_iterator7.s(); !(_step7 = _iterator7.n()).done;) {
                var operand = _step7.value;
                if (typeof operand == "number") ++result;else if (typeof operand == "string") result += (operand.length + 1 + 3) / 4 | 0;else ++result;
              }
            } catch (err) {
              _iterator7.e(err);
            } finally {
              _iterator7.f();
            }
            return result;
          }
        }, {
          key: "largestId",
          get: function get() {
            var maximumId = 0;
            var operandChecker = new OperandChecker(this.operandInfo);
            var _iterator8 = _createForOfIteratorHelper(this.operands),
              _step8;
            try {
              for (_iterator8.s(); !(_step8 = _iterator8.n()).done;) {
                var operand = _step8.value;
                var type = operandChecker.nextComparisonType(operand);
                var idType = ids.get(type);
                if (idType) maximumId = Math.max(maximumId, operand);
              }
            } catch (err) {
              _iterator8.e(err);
            } finally {
              _iterator8.f();
            }
            return maximumId;
          }
        }]);
      }();
    };
    for (_iterator5.s(); !(_step5 = _iterator5.n()).done;) {
      if (_loop()) continue;
    }
  } catch (err) {
    _iterator5.e(err);
  } finally {
    _iterator5.f();
  }
  return result;
}
var SPIRVAssembler = /*#__PURE__*/function () {
  function SPIRVAssembler() {
    _classCallCheck(this, SPIRVAssembler);
    this._largestId = 0;
    this._size = 5;
    this._storage = new Uint32Array(this.size);
    this.storage[0] = 0x07230203; // Magic number
    this.storage[1] = 0x00010000; // Version: 1.0
    this.storage[2] = 0x574B0000; // Tool: "WK"
    this.storage[3] = 0; // Placeholder: All <id>s are less than this value.
    this.storage[4] = 0; // Reserved
  }
  return _createClass(SPIRVAssembler, [{
    key: "append",
    value: function append(op) {
      this._largestId = Math.max(this._largestId, op.largestId);
      var deltaStorageSize = op.storageSize;
      if (this.size + deltaStorageSize > this.storage.length) {
        var newStorageSize = (this.size + deltaStorageSize) * 1.5;
        var newStorage = new Uint32Array(newStorageSize);
        for (var i = 0; i < this.size; ++i) newStorage[i] = this.storage[i];
        this._storage = newStorage;
      }
      if ((deltaStorageSize & 0xFFFF) != deltaStorageSize || (op.opcode & 0xFFFF) != op.opcode) throw new Error("Out of bounds!");
      this.storage[this.size] = (deltaStorageSize & 0xFFFF) << 16 | op.opcode & 0xFFFF;
      ++this._size;
      if (deltaStorageSize <= op.operands.size) throw new Error("The storage size must be greater than the number of parameters");
      for (var _i2 = 0; _i2 < op.operands.length; ++_i2) {
        var operand = op.operands[_i2];
        if (typeof operand == "number") {
          this.storage[this.size] = operand;
          ++this._size;
        } else if (typeof operand == "string") {
          var word = 0;
          for (var j = 0; j < operand.length + 1; ++j) {
            var charCode = void 0;
            if (j < operand.length) charCode = operand.charCodeAt(j);else charCode = 0;
            if (charCode > 0xFF) throw new Error("Non-ASCII strings don't work yet");
            switch (j % 4) {
              case 0:
                word |= charCode;
                break;
              case 1:
                word |= charCode << 8;
                break;
              case 2:
                word |= charCode << 16;
                break;
              case 3:
                word |= charCode << 24;
                this.storage[this.size + (j / 4 | 0)] = word;
                word = 0;
                break;
            }
          }
          if (operand.length % 4 != 0) this.storage[this.size + ((operand.length + 1) / 4 | 0)] = word;
          this._size += (operand.length + 1 + 3) / 4 | 0;
        } else {
          this.storage[this.size] = operand.value;
          ++this._size;
        }
      }
    }
  }, {
    key: "size",
    get: function get() {
      return this._size;
    }
  }, {
    key: "storage",
    get: function get() {
      return this._storage;
    }
  }, {
    key: "result",
    get: function get() {
      this.storage[3] = this._largestId + 1;
      return this.storage.slice(0, this.size);
    }
  }]);
}();