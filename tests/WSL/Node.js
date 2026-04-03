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
var Node = /*#__PURE__*/function () {
  function Node() {
    _classCallCheck(this, Node);
  }
  return _createClass(Node, [{
    key: "visit",
    value: function visit(visitor) {
      var visitFunc = visitor["visit" + this.constructor.name];
      if (!visitFunc) throw new Error("No visit function for " + this.constructor.name + " in " + visitor.constructor.name);
      var returnValue = visitFunc.call(visitor, this);
      if ("returnValue" in visitor) returnValue = visitor.returnValue;
      return returnValue;
    }
  }, {
    key: "unify",
    value: function unify(unificationContext, other) {
      if (!other) throw new Error("Null other");
      var unifyThis = this.unifyNode;
      var unifyOther = other.unifyNode;
      if (unifyThis == unifyOther) return true;
      if (unifyOther.typeVariableUnify(unificationContext, unifyThis)) return true;
      return unifyThis.unifyImpl(unificationContext, unifyOther);
    }
  }, {
    key: "unifyImpl",
    value: function unifyImpl(unificationContext, other) {
      if (other.typeVariableUnify(unificationContext, this)) return true;
      return this == other;
    }
  }, {
    key: "typeVariableUnify",
    value: function typeVariableUnify(unificationContext, other) {
      return false;
    }
  }, {
    key: "_typeVariableUnifyImpl",
    value: function _typeVariableUnifyImpl(unificationContext, other) {
      var realThis = unificationContext.find(this);
      if (realThis != this) return realThis.unify(unificationContext, other);
      unificationContext.union(this, other);
      return true;
    }

    // Most type variables don't care about this.
  }, {
    key: "prepareToVerify",
    value: function prepareToVerify(unificationContext) {}
  }, {
    key: "commitUnification",
    value: function commitUnification(unificationContext) {}
  }, {
    key: "unifyNode",
    get: function get() {
      return this;
    }
  }, {
    key: "isUnifiable",
    get: function get() {
      return false;
    }
  }, {
    key: "isLiteral",
    get: function get() {
      return false;
    }
  }, {
    key: "isNative",
    get: function get() {
      return false;
    }
  }, {
    key: "conversionCost",
    value: function conversionCost(unificationContext) {
      return 0;
    }
  }, {
    key: "equals",
    value: function equals(other) {
      var unificationContext = new UnificationContext();
      if (this.unify(unificationContext, other) && unificationContext.verify().result) return unificationContext;
      return false;
    }
  }, {
    key: "equalsWithCommit",
    value: function equalsWithCommit(other) {
      var unificationContext = this.equals(other);
      if (!unificationContext) return false;
      unificationContext.commit();
      return unificationContext;
    }
  }, {
    key: "commit",
    value: function commit() {
      var unificationContext = new UnificationContext();
      unificationContext.addExtraNode(this);
      var result = unificationContext.verify();
      if (!result.result) throw new WError(node.origin.originString, "Could not infer type: " + result.reason);
      unificationContext.commit();
      return unificationContext.find(this);
    }
  }, {
    key: "substitute",
    value: function substitute(parameters, argumentList) {
      return this.visit(new Substitution(parameters, argumentList));
    }
  }, {
    key: "substituteToUnification",
    value: function substituteToUnification(parameters, unificationContext) {
      return this.substitute(parameters, parameters.map(function (type) {
        return unificationContext.find(type);
      }));
    }
  }], [{
    key: "visit",
    value: function visit(node, visitor) {
      if (node instanceof Node) return node.visit(visitor);
      return node;
    }
  }]);
}();