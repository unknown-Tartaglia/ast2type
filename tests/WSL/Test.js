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
function _slicedToArray(r, e) { return _arrayWithHoles(r) || _iterableToArrayLimit(r, e) || _unsupportedIterableToArray(r, e) || _nonIterableRest(); }
function _nonIterableRest() { throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); }
function _iterableToArrayLimit(r, l) { var t = null == r ? null : "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (null != t) { var e, n, i, u, a = [], f = !0, o = !1; try { if (i = (t = t.call(r)).next, 0 === l) { if (Object(t) !== t) return; f = !1; } else for (; !(f = (e = i.call(t)).done) && (a.push(e.value), a.length !== l); f = !0); } catch (r) { o = !0, n = r; } finally { try { if (!f && null != t.return && (u = t.return(), Object(u) !== u)) return; } finally { if (o) throw n; } } return a; } }
function _arrayWithHoles(r) { if (Array.isArray(r)) return r; }
function _createForOfIteratorHelper(r, e) { var t = "undefined" != typeof Symbol && r[Symbol.iterator] || r["@@iterator"]; if (!t) { if (Array.isArray(r) || (t = _unsupportedIterableToArray(r)) || e && r && "number" == typeof r.length) { t && (r = t); var _n = 0, F = function F() {}; return { s: F, n: function n() { return _n >= r.length ? { done: !0 } : { done: !1, value: r[_n++] }; }, e: function e(r) { throw r; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var o, a = !0, u = !1; return { s: function s() { t = t.call(r); }, n: function n() { var r = t.next(); return a = r.done, r; }, e: function e(r) { u = !0, o = r; }, f: function f() { try { a || null == t.return || t.return(); } finally { if (u) throw o; } } }; }
function _unsupportedIterableToArray(r, a) { if (r) { if ("string" == typeof r) return _arrayLikeToArray(r, a); var t = {}.toString.call(r).slice(8, -1); return "Object" === t && r.constructor && (t = r.constructor.name), "Map" === t || "Set" === t ? Array.from(r) : "Arguments" === t || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(t) ? _arrayLikeToArray(r, a) : void 0; } }
function _arrayLikeToArray(r, a) { (null == a || a > r.length) && (a = r.length); for (var e = 0, n = Array(a); e < a; e++) n[e] = r[e]; return n; }
function doPrep(code) {
  return prepare("/internal/test", 0, code);
}
function doLex(code) {
  var lexer = new Lexer("/internal/test", "native", 0, code);
  var result = [];
  for (;;) {
    var next = lexer.next();
    if (!next) return result;
    result.push(next);
  }
  return result;
}
function makeInt(program, value) {
  return TypedValue.box(program.intrinsics.int32, value);
}
function makeUint(program, value) {
  return TypedValue.box(program.intrinsics.uint32, value);
}
function makeUint8(program, value) {
  return TypedValue.box(program.intrinsics.uint8, value);
}
function makeBool(program, value) {
  return TypedValue.box(program.intrinsics.bool, value);
}
function makeFloat(program, value) {
  return TypedValue.box(program.intrinsics.float, value);
}
function makeDouble(program, value) {
  return TypedValue.box(program.intrinsics.double, value);
}
function makeEnum(program, enumName, value) {
  var enumType = program.types.get(enumName);
  if (!enumType) throw new Error("No type named " + enumName);
  var enumMember = enumType.memberByName(value);
  if (!enumMember) throw new Error("No member named " + enumMember + " in " + enumType);
  return TypedValue.box(enumType, enumMember.value.unifyNode.valueForSelectedType);
}
function checkNumber(program, result, expected) {
  if (!result.type.unifyNode.isNumber) throw new Error("Wrong result type; result: " + result);
  if (result.value != expected) throw new Error("Wrong result: " + result.value + " (expected " + expected + ")");
}
function checkInt(program, result, expected) {
  if (!result.type.equals(program.intrinsics.int32)) throw new Error("Wrong result type; result: " + result);
  checkNumber(program, result, expected);
}
function checkEnum(program, result, expected) {
  if (!(result.type.unifyNode instanceof EnumType)) throw new Error("Wrong result type; result: " + result);
  if (result.value != expected) throw new Error("Wrong result: " + result.value + " (expected " + expected + ")");
}
function checkUint(program, result, expected) {
  if (!result.type.equals(program.intrinsics.uint32)) throw new Error("Wrong result type: " + result.type);
  if (result.value != expected) throw new Error("Wrong result: " + result.value + " (expected " + expected + ")");
}
function checkUint8(program, result, expected) {
  if (!result.type.equals(program.intrinsics.uint8)) throw new Error("Wrong result type: " + result.type);
  if (result.value != expected) throw new Error("Wrong result: " + result.value + " (expected " + expected + ")");
}
function checkBool(program, result, expected) {
  if (!result.type.equals(program.intrinsics.bool)) throw new Error("Wrong result type: " + result.type);
  if (result.value != expected) throw new Error("Wrong result: " + result.value + " (expected " + expected + ")");
}
function checkFloat(program, result, expected) {
  if (!result.type.equals(program.intrinsics.float)) throw new Error("Wrong result type: " + result.type);
  if (result.value != expected) throw new Error("Wrong result: " + result.value + " (expected " + expected + ")");
}
function checkDouble(program, result, expected) {
  if (!result.type.equals(program.intrinsics.double)) throw new Error("Wrong result type: " + result.type);
  if (result.value != expected) throw new Error("Wrong result: " + result.value + " (expected " + expected + ")");
}
function checkLexerToken(result, expectedIndex, expectedKind, expectedText) {
  if (result._index != expectedIndex) throw new Error("Wrong lexer index; result: " + result._index + " (expected " + expectedIndex + ")");
  if (result._kind != expectedKind) throw new Error("Wrong lexer kind; result: " + result._kind + " (expected " + expectedKind + ")");
  if (result._text != expectedText) throw new Error("Wrong lexer text; result: " + result._text + " (expected " + expectedText + ")");
}
function checkFail(callback, predicate) {
  try {
    callback();
    throw new Error("Did not throw exception");
  } catch (e) {
    if (predicate(e)) {
      return;
    }
    throw e;
  }
}
var okToTest = false;
var tests = new Proxy({}, {
  set: function set(target, property, value, receiver) {
    if (property in target) throw new Error("Trying to declare duplicate test: " + property);
    target[property] = value;
    return true;
  }
});
tests.literalBool = function () {
  var program = doPrep("bool foo() { return true; }");
  checkBool(program, callFunction(program, "foo", [], []), true);
};
tests.identityBool = function () {
  var program = doPrep("bool foo(bool x) { return x; }");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false)]), false);
};
tests.intSimpleMath = function () {
  var program = doPrep("int foo(int x, int y) { return x + y; }");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 5)]), 12);
  program = doPrep("int foo(int x, int y) { return x - y; }");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 5)]), 2);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5), makeInt(program, 7)]), -2);
  program = doPrep("int foo(int x, int y) { return x * y; }");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 5)]), 35);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, -5)]), -35);
  program = doPrep("int foo(int x, int y) { return x / y; }");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 2)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, -2)]), -3);
};
tests.uintSimpleMath = function () {
  var program = doPrep("uint foo(uint x, uint y) { return x + y; }");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 5)]), 12);
  program = doPrep("uint foo(uint x, uint y) { return x - y; }");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 5)]), 2);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 5), makeUint(program, 7)]), 4294967294);
  program = doPrep("uint foo(uint x, uint y) { return x * y; }");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 5)]), 35);
  program = doPrep("uint foo(uint x, uint y) { return x / y; }");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 2)]), 3);
};
tests.uint8SimpleMath = function () {
  var program = doPrep("uint8 foo(uint8 x, uint8 y) { return x + y; }");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 5)]), 12);
  program = doPrep("uint8 foo(uint8 x, uint8 y) { return x - y; }");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 5)]), 2);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 5), makeUint8(program, 7)]), 254);
  program = doPrep("uint8 foo(uint8 x, uint8 y) { return x * y; }");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 5)]), 35);
  program = doPrep("uint8 foo(uint8 x, uint8 y) { return x / y; }");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 2)]), 3);
};
tests.equality = function () {
  var program = doPrep("bool foo(uint x, uint y) { return x == y; }");
  checkBool(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 5)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 7)]), true);
  program = doPrep("bool foo(uint8 x, uint8 y) { return x == y; }");
  checkBool(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 5)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 7)]), true);
  program = doPrep("bool foo(int x, int y) { return x == y; }");
  checkBool(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 5)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 7)]), true);
  program = doPrep("bool foo(bool x, bool y) { return x == y; }");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, true)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, false)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, false)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, true)]), true);
};
tests.logicalNegation = function () {
  var program = doPrep("bool foo(bool x) { return !x; }");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false)]), true);
};
tests.notEquality = function () {
  var program = doPrep("bool foo(uint x, uint y) { return x != y; }");
  checkBool(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 5)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeUint(program, 7), makeUint(program, 7)]), false);
  program = doPrep("bool foo(uint8 x, uint8 y) { return x != y; }");
  checkBool(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 5)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeUint8(program, 7), makeUint8(program, 7)]), false);
  program = doPrep("bool foo(int x, int y) { return x != y; }");
  checkBool(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 5)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeInt(program, 7), makeInt(program, 7)]), false);
  program = doPrep("bool foo(bool x, bool y) { return x != y; }");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, true)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, false)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, false)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, true)]), false);
};
tests.equalityTypeFailure = function () {
  checkFail(function () {
    return doPrep("bool foo(int x, uint y) { return x == y; }");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("/internal/test:1") != -1;
  });
};
tests.generalNegation = function () {
  var program = doPrep("bool foo(int x) { return !x; }");
  checkBool(program, callFunction(program, "foo", [], [makeInt(program, 7)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeInt(program, 0)]), true);
};
tests.add1 = function () {
  var program = doPrep("int foo(int x) { return x + 1; }");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 42)]), 43);
};
tests.simpleGeneric = function () {
  var program = doPrep("\n        T id<T>(T x) { return x; }\n        int foo(int x) { return id(x) + 1; }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 42)]), 43);
};
tests.nameResolutionFailure = function () {
  checkFail(function () {
    return doPrep("int foo(int x) { return x + y; }");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("/internal/test:1") != -1;
  });
};
tests.simpleVariable = function () {
  var program = doPrep("\n        int foo(int p)\n        {\n            int result = p;\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 42)]), 42);
};
tests.simpleAssignment = function () {
  var program = doPrep("\n        int foo(int p)\n        {\n            int result;\n            result = p;\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 42)]), 42);
};
tests.simpleDefault = function () {
  var program = doPrep("\n        int foo()\n        {\n            int result;\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 0);
};
tests.simpleDereference = function () {
  var program = doPrep("\n        int foo(device int* p)\n        {\n            return *p;\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 13);
  checkInt(program, callFunction(program, "foo", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]), 13);
};
tests.dereferenceStore = function () {
  var program = doPrep("\n        void foo(device int* p)\n        {\n            *p = 52;\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 13);
  callFunction(program, "foo", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]);
  if (buffer.get(0) != 52) throw new Error("Expected buffer to contain 52 but it contains: " + buffer.get(0));
};
tests.simpleMakePtr = function () {
  var program = doPrep("\n        thread int* foo()\n        {\n            int x = 42;\n            return &x;\n        }\n    ");
  var result = callFunction(program, "foo", [], []);
  if (!result.type.isPtr) throw new Error("Return type is not a pointer: " + result.type);
  if (!result.type.elementType.equals(program.intrinsics.int32)) throw new Error("Return type is not a pointer to an int: " + result.type);
  if (!(result.value instanceof EPtr)) throw new Error("Return value is not an EPtr: " + result.value);
  var value = result.value.loadValue();
  if (value != 42) throw new Error("Expected 42 but got: " + value);
};
tests.threadArrayLoad = function () {
  var program = doPrep("\n        int foo(thread int[] array)\n        {\n            return array[0u];\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 89);
  var result = callFunction(program, "foo", [], [TypedValue.box(new ArrayRefType(externalOrigin, "thread", program.intrinsics.int32), new EArrayRef(new EPtr(buffer, 0), 1))]);
  checkInt(program, result, 89);
};
tests.threadArrayLoadIntLiteral = function () {
  var program = doPrep("\n        int foo(thread int[] array)\n        {\n            return array[0];\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 89);
  var result = callFunction(program, "foo", [], [TypedValue.box(new ArrayRefType(externalOrigin, "thread", program.intrinsics.int32), new EArrayRef(new EPtr(buffer, 0), 1))]);
  checkInt(program, result, 89);
};
tests.deviceArrayLoad = function () {
  var program = doPrep("\n        int foo(device int[] array)\n        {\n            return array[0u];\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 89);
  var result = callFunction(program, "foo", [], [TypedValue.box(new ArrayRefType(externalOrigin, "device", program.intrinsics.int32), new EArrayRef(new EPtr(buffer, 0), 1))]);
  checkInt(program, result, 89);
};
tests.threadArrayStore = function () {
  var program = doPrep("\n        void foo(thread int[] array, int value)\n        {\n            array[0u] = value;\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 15);
  var arrayRef = TypedValue.box(new ArrayRefType(externalOrigin, "thread", program.intrinsics.int32), new EArrayRef(new EPtr(buffer, 0), 1));
  callFunction(program, "foo", [], [arrayRef, makeInt(program, 65)]);
  if (buffer.get(0) != 65) throw new Error("Bad value stored into buffer (expected 65): " + buffer.get(0));
  callFunction(program, "foo", [], [arrayRef, makeInt(program, -111)]);
  if (buffer.get(0) != -111) throw new Error("Bad value stored into buffer (expected -111): " + buffer.get(0));
};
tests.deviceArrayStore = function () {
  var program = doPrep("\n        void foo(device int[] array, int value)\n        {\n            array[0u] = value;\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 15);
  var arrayRef = TypedValue.box(new ArrayRefType(externalOrigin, "device", program.intrinsics.int32), new EArrayRef(new EPtr(buffer, 0), 1));
  callFunction(program, "foo", [], [arrayRef, makeInt(program, 65)]);
  if (buffer.get(0) != 65) throw new Error("Bad value stored into buffer (expected 65): " + buffer.get(0));
  callFunction(program, "foo", [], [arrayRef, makeInt(program, -111)]);
  if (buffer.get(0) != -111) throw new Error("Bad value stored into buffer (expected -111): " + buffer.get(0));
};
tests.deviceArrayStoreIntLiteral = function () {
  var program = doPrep("\n        void foo(device int[] array, int value)\n        {\n            array[0] = value;\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 15);
  var arrayRef = TypedValue.box(new ArrayRefType(externalOrigin, "device", program.intrinsics.int32), new EArrayRef(new EPtr(buffer, 0), 1));
  callFunction(program, "foo", [], [arrayRef, makeInt(program, 65)]);
  if (buffer.get(0) != 65) throw new Error("Bad value stored into buffer (expected 65): " + buffer.get(0));
  callFunction(program, "foo", [], [arrayRef, makeInt(program, -111)]);
  if (buffer.get(0) != -111) throw new Error("Bad value stored into buffer (expected -111): " + buffer.get(0));
};
tests.simpleProtocol = function () {
  var program = doPrep("\n        protocol MyAddable {\n            MyAddable operator+(MyAddable, MyAddable);\n        }\n        T add<T:MyAddable>(T a, T b)\n        {\n            return a + b;\n        }\n        int foo(int x)\n        {\n            return add(x, 73);\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 45)]), 45 + 73);
};
tests.typeMismatchReturn = function () {
  checkFail(function () {
    return doPrep("\n            int foo()\n            {\n                return 0u;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.typeMismatchVariableDecl = function () {
  checkFail(function () {
    return doPrep("\n            void foo(uint x)\n            {\n                int y = x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.typeMismatchAssignment = function () {
  checkFail(function () {
    return doPrep("\n            void foo(uint x)\n            {\n                int y;\n                y = x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.typeMismatchReturnParam = function () {
  checkFail(function () {
    return doPrep("\n            int foo(uint x)\n            {\n                return x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.badAdd = function () {
  checkFail(function () {
    return doPrep("\n            void bar<T>(T) { }\n            void foo(int x, uint y)\n            {\n                bar(x + y);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("native int32 operator+<>(int32,int32)") != -1;
  });
};
tests.lexerKeyword = function () {
  var result = doLex("ident for while 123 123u { } {asd asd{ 1a3 1.2 + 3.4 + 1. + .2 1.2d 0.d .3d && ||");
  if (result.length != 25) throw new Error("Lexer emitted an incorrect number of tokens (expected 23): " + result.length);
  checkLexerToken(result[0], 0, "identifier", "ident");
  checkLexerToken(result[1], 6, "keyword", "for");
  checkLexerToken(result[2], 10, "keyword", "while");
  checkLexerToken(result[3], 16, "intLiteral", "123");
  checkLexerToken(result[4], 20, "uintLiteral", "123u");
  checkLexerToken(result[5], 25, "punctuation", "{");
  checkLexerToken(result[6], 27, "punctuation", "}");
  checkLexerToken(result[7], 29, "punctuation", "{");
  checkLexerToken(result[8], 30, "identifier", "asd");
  checkLexerToken(result[9], 34, "identifier", "asd");
  checkLexerToken(result[10], 37, "punctuation", "{");
  checkLexerToken(result[11], 39, "intLiteral", "1");
  checkLexerToken(result[12], 40, "identifier", "a3");
  checkLexerToken(result[13], 43, "floatLiteral", "1.2");
  checkLexerToken(result[14], 47, "punctuation", "+");
  checkLexerToken(result[15], 49, "floatLiteral", "3.4");
  checkLexerToken(result[16], 53, "punctuation", "+");
  checkLexerToken(result[17], 55, "floatLiteral", "1.");
  checkLexerToken(result[18], 58, "punctuation", "+");
  checkLexerToken(result[19], 60, "floatLiteral", ".2");
  checkLexerToken(result[20], 63, "floatLiteral", "1.2d");
  checkLexerToken(result[21], 68, "floatLiteral", "0.d");
  checkLexerToken(result[22], 72, "floatLiteral", ".3d");
  checkLexerToken(result[23], 76, "punctuation", "&&");
  checkLexerToken(result[24], 79, "punctuation", "||");
};
tests.simpleNoReturn = function () {
  checkFail(function () {
    return doPrep("int foo() { }");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.simpleUnreachableCode = function () {
  checkFail(function () {
    return doPrep("\n            void foo()\n            {\n                return;\n                int x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.simpleStruct = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n            int y;\n        }\n        Foo foo(Foo foo)\n        {\n            Foo result;\n            result.x = foo.y;\n            result.y = foo.x;\n            return result;\n        }\n    ");
  var structType = program.types.get("Foo");
  if (!structType) throw new Error("Did not find Foo type");
  var buffer = new EBuffer(2);
  buffer.set(0, 62);
  buffer.set(1, 24);
  var result = callFunction(program, "foo", [], [new TypedValue(structType, new EPtr(buffer, 0))]);
  if (!result.type.equals(structType)) throw new Error("Wrong result type: " + result.type);
  var x = result.ePtr.get(0);
  var y = result.ePtr.get(1);
  if (x != 24) throw new Error("Wrong result for x: " + x + " (y = " + y + ")");
  if (y != 62) throw new Error("Wrong result for y: " + y + " (x + " + x + ")");
};
tests.genericStructInstance = function () {
  var program = doPrep("\n        struct Foo<T> {\n            T x;\n            T y;\n        }\n        Foo<int> foo(Foo<int> foo)\n        {\n            Foo<int> result;\n            result.x = foo.y;\n            result.y = foo.x;\n            return result;\n        }\n    ");
  var structType = TypeRef.instantiate(program.types.get("Foo"), [program.intrinsics.int32]);
  var buffer = new EBuffer(2);
  buffer.set(0, 62);
  buffer.set(1, 24);
  var result = callFunction(program, "foo", [], [new TypedValue(structType, new EPtr(buffer, 0))]);
  var x = result.ePtr.get(0);
  var y = result.ePtr.get(1);
  if (x != 24) throw new Error("Wrong result for x: " + x + " (y = " + y + ")");
  if (y != 62) throw new Error("Wrong result for y: " + y + " (x + " + x + ")");
};
tests.doubleGenericCallsDoubleGeneric = function () {
  doPrep("\n        void foo<T, U>(T, U) { }\n        void bar<V, W>(V x, W y) { foo(x, y); }\n    ");
};
tests.doubleGenericCallsSingleGeneric = function () {
  checkFail(function () {
    return doPrep("\n            void foo<T>(T, T) { }\n            void bar<V, W>(V x, W y) { foo(x, y); }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.loadNull = function () {
  checkFail(function () {
    return doPrep("\n            void sink<T>(T) { }\n            void foo() { sink(*null); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Type passed to dereference is not a pointer: null") != -1;
  });
};
tests.storeNull = function () {
  checkFail(function () {
    return doPrep("\n            void foo() { *null = 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Type passed to dereference is not a pointer: null") != -1;
  });
};
tests.returnNull = function () {
  var program = doPrep("\n        thread int* foo() { return null; }\n    ");
  var result = callFunction(program, "foo", [], []);
  if (!result.type.isPtr) throw new Error("Return type is not a pointer: " + result.type);
  if (!result.type.elementType.equals(program.intrinsics.int32)) throw new Error("Return type is not a pointer to an int: " + result.type);
  if (result.value != null) throw new Error("Return value is not null: " + result.value);
};
tests.dereferenceDefaultNull = function () {
  var program = doPrep("\n        int foo()\n        {\n            thread int* p;\n            return *p;\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "foo", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.defaultInitializedNull = function () {
  var program = doPrep("\n        int foo()\n        {\n            thread int* p = null;;\n            return *p;\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "foo", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.passNullToPtrMonomorphic = function () {
  var program = doPrep("\n        int foo(thread int* ptr)\n        {\n            return *ptr;\n        }\n        int bar()\n        {\n            return foo(null);\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "bar", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.passNullToPtrPolymorphic = function () {
  checkFail(function () {
    return doPrep("\n            T foo<T>(thread T* ptr)\n            {\n                return *ptr;\n            }\n            int bar()\n            {\n                return foo(null);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.passNullToPolymorphic = function () {
  checkFail(function () {
    return doPrep("\n            T foo<T>(T ptr)\n            {\n                return ptr;\n            }\n            int bar()\n            {\n                return foo(null);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.loadNullArrayRef = function () {
  checkFail(function () {
    return doPrep("\n            void sink<T>(T) { }\n            void foo() { sink(null[0u]); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Cannot resolve access") != -1;
  });
};
tests.storeNullArrayRef = function () {
  checkFail(function () {
    return doPrep("\n            void foo() { null[0u] = 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Cannot resolve access") != -1;
  });
};
tests.returnNullArrayRef = function () {
  var program = doPrep("\n        thread int[] foo() { return null; }\n    ");
  var result = callFunction(program, "foo", [], []);
  if (!result.type.isArrayRef) throw new Error("Return type is not an array reference: " + result.type);
  if (!result.type.elementType.equals(program.intrinsics.int32)) throw new Error("Return type is not an int array reference: " + result.type);
  if (result.value != null) throw new Error("Return value is not null: " + result.value);
};
tests.dereferenceDefaultNullArrayRef = function () {
  var program = doPrep("\n        int foo()\n        {\n            thread int[] p;\n            return p[0u];\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "foo", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.defaultInitializedNullArrayRef = function () {
  var program = doPrep("\n        int foo()\n        {\n            thread int[] p = null;\n            return p[0u];\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "foo", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.defaultInitializedNullArrayRefIntLiteral = function () {
  var program = doPrep("\n        int foo()\n        {\n            thread int[] p = null;\n            return p[0];\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "foo", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.passNullToPtrMonomorphicArrayRef = function () {
  var program = doPrep("\n        int foo(thread int[] ptr)\n        {\n            return ptr[0u];\n        }\n        int bar()\n        {\n            return foo(null);\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "bar", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.passNullToPtrPolymorphicArrayRef = function () {
  checkFail(function () {
    return doPrep("\n            T foo<T>(thread T[] ptr)\n            {\n                return ptr[0u];\n            }\n            int bar()\n            {\n                return foo(null);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.returnIntLiteralUint = function () {
  var program = doPrep("uint foo() { return 42; }");
  checkNumber(program, callFunction(program, "foo", [], []), 42);
};
tests.returnIntLiteralDouble = function () {
  var program = doPrep("double foo() { return 42; }");
  checkNumber(program, callFunction(program, "foo", [], []), 42);
};
tests.badIntLiteralForInt = function () {
  checkFail(function () {
    return doPrep("void foo() { int x = 3000000000; }");
  }, function (e) {
    return e instanceof WSyntaxError;
  });
};
tests.badIntLiteralForUint = function () {
  checkFail(function () {
    return doPrep("void foo() { uint x = 5000000000; }");
  }, function (e) {
    return e instanceof WSyntaxError;
  });
};
tests.badIntLiteralForDouble = function () {
  checkFail(function () {
    return doPrep("void foo() { double x = 5000000000000000000000000000000000000; }");
  }, function (e) {
    return e instanceof WSyntaxError;
  });
};
tests.passNullAndNotNull = function () {
  var program = doPrep("\n        T bar<T>(device T* p, device T*)\n        {\n            return *p;\n        }\n        int foo(device int* p)\n        {\n            return bar(p, null);\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 13);
  checkInt(program, callFunction(program, "foo", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]), 13);
};
tests.passNullAndNotNullFullPoly = function () {
  var program = doPrep("\n        T bar<T>(T p, T)\n        {\n            return p;\n        }\n        int foo(device int* p)\n        {\n            return *bar(p, null);\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 13);
  checkInt(program, callFunction(program, "foo", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]), 13);
};
tests.passNullAndNotNullFullPolyReverse = function () {
  var program = doPrep("\n        T bar<T>(T, T p)\n        {\n            return p;\n        }\n        int foo(device int* p)\n        {\n            return *bar(null, p);\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 13);
  checkInt(program, callFunction(program, "foo", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]), 13);
};
tests.nullTypeVariableUnify = function () {
  var left = new NullType(externalOrigin);
  var right = new TypeVariable(externalOrigin, "T", null);
  if (left.equals(right)) throw new Error("Should not be equal but are: " + left + " and " + right);
  if (right.equals(left)) throw new Error("Should not be equal but are: " + left + " and " + right);
  function everyOrder(array, callback) {
    function recurse(array, callback, order) {
      if (!array.length) return callback.call(null, order);
      for (var i = 0; i < array.length; ++i) {
        var nextArray = array.concat();
        nextArray.splice(i, 1);
        recurse(nextArray, callback, order.concat([array[i]]));
      }
    }
    recurse(array, callback, []);
  }
  function everyPair(things) {
    var result = [];
    for (var i = 0; i < things.length; ++i) {
      for (var j = 0; j < things.length; ++j) {
        if (i != j) result.push([things[i], things[j]]);
      }
    }
    return result;
  }
  everyOrder(everyPair(["nullType", "variableType", "ptrType"]), function (order) {
    var types = {};
    types.nullType = new NullType(externalOrigin);
    types.variableType = new TypeVariable(externalOrigin, "T", null);
    types.ptrType = new PtrType(externalOrigin, "constant", new NativeType(externalOrigin, "foo_t", []));
    var unificationContext = new UnificationContext([types.variableType]);
    var _iterator = _createForOfIteratorHelper(order),
      _step;
    try {
      for (_iterator.s(); !(_step = _iterator.n()).done;) {
        var _step$value = _slicedToArray(_step.value, 2),
          leftName = _step$value[0],
          rightName = _step$value[1];
        var _left = types[leftName];
        var _right = types[rightName];
        var result = _left.unify(unificationContext, _right);
        if (!result) throw new Error("In order " + order + " cannot unify " + _left + " with " + _right);
      }
    } catch (err) {
      _iterator.e(err);
    } finally {
      _iterator.f();
    }
    if (!unificationContext.verify().result) throw new Error("In order " + order.map(function (value) {
      return "(" + value + ")";
    }) + " cannot verify");
  });
};
tests.doubleNot = function () {
  var program = doPrep("\n        bool foo(bool x)\n        {\n            return !!x;\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false)]), false);
};
tests.simpleRecursion = function () {
  checkFail(function () {
    return doPrep("\n            void foo<T>(T x)\n            {\n                foo(&x);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.protocolMonoSigPolyDef = function () {
  var program = doPrep("\n        struct IntAnd<T> {\n            int first;\n            T second;\n        }\n        IntAnd<T> intAnd<T>(int first, T second)\n        {\n            IntAnd<T> result;\n            result.first = first;\n            result.second = second;\n            return result;\n        }\n        protocol IntAndable {\n            IntAnd<int> intAnd(IntAndable, int);\n        }\n        int foo<T:IntAndable>(T first, int second)\n        {\n            IntAnd<int> result = intAnd(first, second);\n            return result.first + result.second;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 54), makeInt(program, 12)]), 54 + 12);
};
tests.protocolPolySigPolyDef = function () {
  var program = doPrep("\n        struct IntAnd<T> {\n            int first;\n            T second;\n        }\n        IntAnd<T> intAnd<T>(int first, T second)\n        {\n            IntAnd<T> result;\n            result.first = first;\n            result.second = second;\n            return result;\n        }\n        protocol IntAndable {\n            IntAnd<T> intAnd<T>(IntAndable, T);\n        }\n        int foo<T:IntAndable>(T first, int second)\n        {\n            IntAnd<int> result = intAnd(first, second);\n            return result.first + result.second;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 54), makeInt(program, 12)]), 54 + 12);
};
tests.protocolDoublePolySigDoublePolyDef = function () {
  var program = doPrep("\n        struct IntAnd<T, U> {\n            int first;\n            T second;\n            U third;\n        }\n        IntAnd<T, U> intAnd<T, U>(int first, T second, U third)\n        {\n            IntAnd<T, U> result;\n            result.first = first;\n            result.second = second;\n            result.third = third;\n            return result;\n        }\n        protocol IntAndable {\n            IntAnd<T, U> intAnd<T, U>(IntAndable, T, U);\n        }\n        int foo<T:IntAndable>(T first, int second, int third)\n        {\n            IntAnd<int, int> result = intAnd(first, second, third);\n            return result.first + result.second + result.third;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 54), makeInt(program, 12), makeInt(program, 39)]), 54 + 12 + 39);
};
tests.protocolDoublePolySigDoublePolyDefExplicit = function () {
  var program = doPrep("\n        struct IntAnd<T, U> {\n            int first;\n            T second;\n            U third;\n        }\n        IntAnd<T, U> intAnd<T, U>(int first, T second, U third)\n        {\n            IntAnd<T, U> result;\n            result.first = first;\n            result.second = second;\n            result.third = third;\n            return result;\n        }\n        protocol IntAndable {\n            IntAnd<T, U> intAnd<T, U>(IntAndable, T, U);\n        }\n        int foo<T:IntAndable>(T first, int second, int third)\n        {\n            IntAnd<int, int> result = intAnd<int, int>(first, second, third);\n            return result.first + result.second + result.third;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 54), makeInt(program, 12), makeInt(program, 39)]), 54 + 12 + 39);
};
tests.variableShadowing = function () {
  var program = doPrep("\n        int foo()\n        {\n            int y;\n            int x = 7;\n            {\n                int x = 8;\n                y = x;\n            }\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 8);
  program = doPrep("\n        int foo()\n        {\n            int y;\n            int x = 7;\n            {\n                int x = 8;\n            }\n            y = x;\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 7);
};
tests.ifStatement = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            int y = 6;\n            if (x == 7) {\n                y = 8;\n            }\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 8)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 9)]), 6);
};
tests.ifElseStatement = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            int y = 6;\n            if (x == 7) {\n                y = 8;\n            } else {\n                y = 9;\n            }\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 8)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 9)]), 9);
};
tests.ifElseIfStatement = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            int y = 6;\n            if (x == 7) {\n                y = 8;\n            } else if (x == 8) {\n                y = 9;\n            }\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 8)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 9)]), 6);
};
tests.ifElseIfElseStatement = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            int y = 6;\n            if (x == 7) {\n                y = 8;\n            } else if (x == 8) {\n                y = 9;\n            } else {\n                y = 10;\n            }\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 8)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 9)]), 10);
};
tests.returnIf = function () {
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                int y = 6;\n                if (x == 7) {\n                    return y;\n                }\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                int y = 6;\n                if (x == 7) {\n                    return y;\n                } else {\n                    y = 8;\n                }\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                int y = 6;\n                if (x == 7) {\n                    y = 8;\n                } else {\n                    return y;\n                }\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  var program = doPrep("\n        int foo(int x)\n        {\n            int y = 6;\n            if (x == 7) {\n                return 8;\n            } else {\n                return 10;\n            }\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 8)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 9)]), 10);
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                int y = 6;\n                if (x == 7) {\n                    return 8;\n                } else if (x == 9) {\n                    return 10;\n                }\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  program = doPrep("\n        int foo(int x)\n        {\n            int y = 6;\n            if (x == 7) {\n                return 8;\n            } else {\n                y = 9;\n            }\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 8)]), 9);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 9)]), 9);
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                int y = 6;\n                if (x == 7) {\n                    return 8;\n                } else {\n                    return 10;\n                }\n                return 11;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  program = doPrep("\n        int foo(int x)\n        {\n            int y = 6;\n            if (x == 7)\n                int y = 8;\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 6);
};
tests.simpleWhile = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            while (x < 13)\n                x = x * 2;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 16);
};
tests.protocolMonoPolySigDoublePolyDefExplicit = function () {
  checkFail(function () {
    var program = doPrep("\n                struct IntAnd<T, U> {\n                    int first;\n                    T second;\n                    U third;\n                }\n                IntAnd<T, U> intAnd<T, U>(int first, T second, U third)\n                {\n                    IntAnd<T, U> result;\n                    result.first = first;\n                    result.second = second;\n                    result.third = third;\n                    return result;\n                }\n                protocol IntAndable {\n                    IntAnd<T, int> intAnd<T>(IntAndable, T, int);\n                }\n                int foo<T:IntAndable>(T first, int second, int third)\n                {\n                    IntAnd<int, int> result = intAnd<int>(first, second, third);\n                    return result.first + result.second + result.third;\n                }\n            ");
    callFunction(program, "foo", [], [makeInt(program, 54), makeInt(program, 12), makeInt(program, 39)]);
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.ambiguousOverloadSimple = function () {
  checkFail(function () {
    return doPrep("\n            void foo<T>(int, T) { }\n            void foo<T>(T, int) { }\n            void bar(int a, int b) { foo(a, b); }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.ambiguousOverloadOverlapping = function () {
  checkFail(function () {
    return doPrep("\n            void foo<T>(int, T) { }\n            void foo<T>(T, T) { }\n            void bar(int a, int b) { foo(a, b); }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.ambiguousOverloadTieBreak = function () {
  doPrep("\n        void foo<T>(int, T) { }\n        void foo<T>(T, T) { }\n        void foo(int, int) { }\n        void bar(int a, int b) { foo(a, b); }\n    ");
};
tests.intOverloadResolution = function () {
  var program = doPrep("\n        int foo(int) { return 1; }\n        int foo(uint) { return 2; }\n        int foo(double) { return 3; }\n        int bar() { return foo(42); }\n    ");
  checkInt(program, callFunction(program, "bar", [], []), 1);
};
tests.intOverloadResolutionReverseOrder = function () {
  var program = doPrep("\n        int foo(double) { return 3; }\n        int foo(uint) { return 2; }\n        int foo(int) { return 1; }\n        int bar() { return foo(42); }\n    ");
  checkInt(program, callFunction(program, "bar", [], []), 1);
};
tests.intOverloadResolutionGeneric = function () {
  var program = doPrep("\n        int foo(int) { return 1; }\n        int foo<T>(T) { return 2; }\n        int bar() { return foo(42); }\n    ");
  checkInt(program, callFunction(program, "bar", [], []), 1);
};
tests.intLiteralGeneric = function () {
  var program = doPrep("\n        int foo<T>(T x) { return 3478; }\n        int bar() { return foo(42); }\n    ");
  checkInt(program, callFunction(program, "bar", [], []), 3478);
};
tests.intLiteralGenericWithProtocols = function () {
  var program = doPrep("\n        protocol MyConvertibleToInt {\n            operator int(MyConvertibleToInt);\n        }\n        int foo<T:MyConvertibleToInt>(T x) { return int(x); }\n        int bar() { return foo(42); }\n    ");
  checkInt(program, callFunction(program, "bar", [], []), 42);
};
tests.uintLiteralGeneric = function () {
  var program = doPrep("\n        int foo<T>(T x) { return 3478; }\n        int bar() { return foo(42u); }\n    ");
  checkInt(program, callFunction(program, "bar", [], []), 3478);
};
tests.uintLiteralGenericWithProtocols = function () {
  var program = doPrep("\n        protocol MyConvertibleToUint {\n            operator uint(MyConvertibleToUint);\n        }\n        uint foo<T:MyConvertibleToUint>(T x) { return uint(x); }\n        uint bar() { return foo(42u); }\n    ");
  checkUint(program, callFunction(program, "bar", [], []), 42);
};
tests.intLiteralGenericSpecific = function () {
  var program = doPrep("\n        T foo<T>(T x) { return x; }\n        int bar() { return foo(int(42)); }\n    ");
  checkInt(program, callFunction(program, "bar", [], []), 42);
};
tests.simpleConstexpr = function () {
  var program = doPrep("\n        int foo<int a>(int b)\n        {\n            return a + b;\n        }\n        int bar(int b)\n        {\n            return foo<42>(b);\n        }\n    ");
  checkInt(program, callFunction(program, "bar", [], [makeInt(program, 58)]), 58 + 42);
};
tests.break = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            while (true) {\n                x = x * 2;\n                if (x >= 7)\n                    break;\n            }\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 10)]), 20);
  program = doPrep("\n        int foo(int x)\n        {\n            while (true) {\n                while (true) {\n                    x = x * 2;\n                    if (x >= 7)\n                        break;\n                }\n                x = x - 1;\n                break;\n            }\n            return x;\n            \n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 10)]), 19);
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                while (true) {\n                    {\n                        break;\n                    }\n                    x = x + 1;\n                }\n                return x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                break;\n                return x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  program = doPrep("\n            int foo(int x)\n            {\n                while (true) {\n                    if (x == 7) {\n                        break;\n                    }\n                    x = x + 1;\n                }\n                return x;\n            }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 7);
  program = doPrep("\n            int foo(int x)\n            {\n                while (true) {\n                    break;\n                }\n                return x;\n            }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 1);
  program = doPrep("\n            int foo()\n            {\n                while (true) {\n                    return 7;\n                }\n            }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 7);
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                while(true) {\n                    break;\n                    return 7;\n                }\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.continue = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            while (x < 10) {\n                if (x == 8) {\n                    x = x + 1;\n                    continue;\n                }\n                x = x * 2;\n            }\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 18);
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                continue;\n                return x;\n                \n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.doWhile = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            int y = 7;\n            do {\n                y = 8;\n                break;\n            } while (x < 10);\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 8);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 11)]), 8);
  program = doPrep("\n        int foo(int x)\n        {\n            int y = 7;\n            do {\n                y = 8;\n                break;\n            } while (y == 7);\n            return y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), 8);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            do {\n                if (x == 11) {\n                    x = 15;\n                    continue;\n                }\n                sum = sum + x;\n                x = x + 1;\n            } while (x < 13);\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 9)]), 19);
};
tests.forLoop = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            int i;\n            for (i = 0; i < x; i = i + 1) {\n                sum = sum + i;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            for (int i = 0; i < x; i = i + 1) {\n                sum = sum + i;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            int i = 100;\n            for (int i = 0; i < x; i = i + 1) {\n                sum = sum + i;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            for (int i = 0; i < x; i = i + 1) {\n                if (i == 4)\n                    continue;\n                sum = sum + i;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 11);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            for (int i = 0; i < x; i = i + 1) {\n                if (i == 5)\n                    break;\n                sum = sum + i;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 10);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            for (int i = 0; ; i = i + 1) {\n                if (i >= x)\n                    break;\n                sum = sum + i;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 15);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 21);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            int i = 0;\n            for ( ; ; i = i + 1) {\n                if (i >= x)\n                    break;\n                sum = sum + i;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 15);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 21);
  program = doPrep("\n        int foo(int x)\n        {\n            int sum = 0;\n            int i = 0;\n            for ( ; ; ) {\n                if (i >= x)\n                    break;\n                sum = sum + i;\n                i = i + 1;\n            }\n            return sum;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 3);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 10);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 15);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 21);
  checkFail(function () {
    return doPrep("\n            void foo(int x)\n            {\n                for (int i = 0; ; i = i + 1) {\n                    break;\n                    x = i;\n                }\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  program = doPrep("\n        int foo(int x)\n        {\n            for ( ; ; ) {\n                return 7;\n            }\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 7);
  checkFail(function () {
    return doPrep("\n            int foo(int x)\n            {\n                for ( ; x < 10; ) {\n                    return 7;\n                }\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  program = doPrep("\n        int foo(int x)\n        {\n            for ( ; true; ) {\n                return 7;\n            }\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 3)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 4)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 5)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 6)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 7)]), 7);
};
tests.chainConstexpr = function () {
  var program = doPrep("\n        int foo<int a>(int b)\n        {\n            return a + b;\n        }\n        int bar<int a>(int b)\n        {\n            return foo<a>(b);\n        }\n        int baz(int b)\n        {\n            return bar<42>(b);\n        }\n    ");
  checkInt(program, callFunction(program, "baz", [], [makeInt(program, 58)]), 58 + 42);
};
tests.chainGeneric = function () {
  var program = doPrep("\n        T foo<T>(T x)\n        {\n            return x;\n        }\n        T bar<T>(thread T* ptr)\n        {\n            return *foo(ptr);\n        }\n        int baz(int x)\n        {\n            return bar(&x);\n        }\n    ");
  checkInt(program, callFunction(program, "baz", [], [makeInt(program, 37)]), 37);
};
tests.chainStruct = function () {
  var program = doPrep("\n        struct Foo<T> {\n            T f;\n        }\n        struct Bar<T> {\n            Foo<thread T*> f;\n        }\n        int foo(thread Bar<int>* x)\n        {\n            return *x->f.f;\n        }\n        int bar(int a)\n        {\n            Bar<int> x;\n            x.f.f = &a;\n            return foo(&x);\n        }\n    ");
  checkInt(program, callFunction(program, "bar", [], [makeInt(program, 4657)]), 4657);
};
tests.chainStructNewlyValid = function () {
  var program = doPrep("\n        struct Foo<T> {\n            T f;\n        }\n        struct Bar<T> {\n            Foo<device T*> f;\n        }\n        int foo(thread Bar<int>* x)\n        {\n            return *x->f.f;\n        }\n        int bar(device int* a)\n        {\n            Bar<int> x;\n            x.f.f = a;\n            return foo(&x);\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 78453);
  checkInt(program, callFunction(program, "bar", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]), 78453);
};
tests.chainStructDevice = function () {
  var program = doPrep("\n        struct Foo<T> {\n            T f;\n        }\n        struct Bar<T> {\n            Foo<device T*> f;\n        }\n        int foo(thread Bar<int>* x)\n        {\n            return *x->f.f;\n        }\n        int bar(device int* a)\n        {\n            Bar<int> x;\n            x.f.f = a;\n            return foo(&x);\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 79201);
  checkInt(program, callFunction(program, "bar", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]), 79201);
};
tests.paramChainStructDevice = function () {
  var program = doPrep("\n        struct Foo<T> {\n            T f;\n        }\n        struct Bar<T> {\n            Foo<T> f;\n        }\n        int foo(thread Bar<device int*>* x)\n        {\n            return *x->f.f;\n        }\n        int bar(device int* a)\n        {\n            Bar<device int*> x;\n            x.f.f = a;\n            return foo(&x);\n        }\n    ");
  var buffer = new EBuffer(1);
  buffer.set(0, 79201);
  checkInt(program, callFunction(program, "bar", [], [TypedValue.box(new PtrType(externalOrigin, "device", program.intrinsics.int32), new EPtr(buffer, 0))]), 79201);
};
tests.simpleProtocolExtends = function () {
  var program = doPrep("\n        protocol Foo {\n            void foo(thread Foo*);\n        }\n        protocol Bar : Foo {\n            void bar(thread Bar*);\n        }\n        void fuzz<T:Foo>(thread T* p)\n        {\n            foo(p);\n        }\n        void buzz<T:Bar>(thread T* p)\n        {\n            fuzz(p);\n            bar(p);\n        }\n        void foo(thread int* p)\n        {\n            *p = *p + 743;\n        }\n        void bar(thread int* p)\n        {\n            *p = *p + 91;\n        }\n        int thingy(int a)\n        {\n            buzz(&a);\n            return a;\n        }\n    ");
  checkInt(program, callFunction(program, "thingy", [], [makeInt(program, 642)]), 642 + 743 + 91);
};
tests.protocolExtendsTwo = function () {
  var program = doPrep("\n        protocol Foo {\n            void foo(thread Foo*);\n        }\n        protocol Bar {\n            void bar(thread Bar*);\n        }\n        protocol Baz : Foo, Bar {\n            void baz(thread Baz*);\n        }\n        void fuzz<T:Foo>(thread T* p)\n        {\n            foo(p);\n        }\n        void buzz<T:Bar>(thread T* p)\n        {\n            bar(p);\n        }\n        void xuzz<T:Baz>(thread T* p)\n        {\n            fuzz(p);\n            buzz(p);\n            baz(p);\n        }\n        void foo(thread int* p)\n        {\n            *p = *p + 743;\n        }\n        void bar(thread int* p)\n        {\n            *p = *p + 91;\n        }\n        void baz(thread int* p)\n        {\n            *p = *p + 39;\n        }\n        int thingy(int a)\n        {\n            xuzz(&a);\n            return a;\n        }\n    ");
  checkInt(program, callFunction(program, "thingy", [], [makeInt(program, 642)]), 642 + 743 + 91 + 39);
};
tests.prefixPlusPlus = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            ++x;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 65);
};
tests.prefixPlusPlusResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return ++x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 65);
};
tests.postfixPlusPlus = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            x++;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 65);
};
tests.postfixPlusPlusResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return x++;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 64);
};
tests.prefixMinusMinus = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            --x;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 63);
};
tests.prefixMinusMinusResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return --x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 63);
};
tests.postfixMinusMinus = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            x--;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 63);
};
tests.postfixMinusMinusResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return x--;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 64)]), 64);
};
tests.plusEquals = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            x += 42;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 + 42);
};
tests.plusEqualsResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return x += 42;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 + 42);
};
tests.minusEquals = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            x -= 42;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 - 42);
};
tests.minusEqualsResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return x -= 42;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 - 42);
};
tests.timesEquals = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            x *= 42;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 * 42);
};
tests.timesEqualsResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return x *= 42;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 * 42);
};
tests.divideEquals = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            x /= 42;\n            return x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 / 42 | 0);
};
tests.divideEqualsResult = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            return x /= 42;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 385)]), 385 / 42 | 0);
};
tests.twoIntLiterals = function () {
  var program = doPrep("\n        bool foo()\n        {\n            return 42 == 42;\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], []), true);
};
tests.unifyDifferentLiterals = function () {
  checkFail(function () {
    return doPrep("\n            void bar<T>(T, T)\n            {\n            }\n            void foo()\n            {\n                bar(42, 42u);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.unifyDifferentLiteralsBackwards = function () {
  checkFail(function () {
    return doPrep("\n            void bar<T>(T, T)\n            {\n            }\n            void foo()\n            {\n                bar(42u, 42);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.unifyVeryDifferentLiterals = function () {
  checkFail(function () {
    return doPrep("\n            void bar<T>(T, T)\n            {\n            }\n            void foo()\n            {\n                bar(42, null);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.unifyVeryDifferentLiteralsBackwards = function () {
  checkFail(function () {
    return doPrep("\n            void bar<T>(T, T)\n            {\n            }\n            void foo()\n            {\n                bar(null, 42);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.assignUintToInt = function () {
  checkFail(function () {
    return doPrep("\n            void foo()\n            {\n                int x = 42u;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Type mismatch in variable initialization") != -1;
  });
};
tests.buildArrayThenSumIt = function () {
  var program = doPrep("\n        int foo()\n        {\n            int[42] array;\n            for (uint i = 0; i < 42; i = i + 1)\n                array[i] = int(i + 5);\n            int result;\n            for (uint i = 0; i < 42; i = i + 1)\n                result = result + array[i];\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 42 * 5 + 42 * 41 / 2);
};
tests.buildArrayThenSumItUsingArrayReference = function () {
  var program = doPrep("\n        int bar(thread int[] array)\n        {\n            for (uint i = 0; i < 42; i = i + 1)\n                array[i] = int(i + 5);\n            int result;\n            for (uint i = 0; i < 42; i = i + 1)\n                result = result + array[i];\n            return result;\n        }\n        int foo()\n        {\n            int[42] array;\n            return bar(@array);\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 42 * 5 + 42 * 41 / 2);
};
tests.overrideSubscriptStruct = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n            int y;\n        }\n        thread int* operator&[](thread Foo* foo, uint index)\n        {\n            if (index == 0)\n                return &foo->x;\n            if (index == 1)\n                return &foo->y;\n            return null;\n        }\n        int foo()\n        {\n            Foo foo;\n            foo.x = 498;\n            foo.y = 19;\n            return foo[0] + foo[1] * 3;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 498 + 19 * 3);
};
tests.overrideSubscriptStructAndDoStores = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n            int y;\n        }\n        thread int* operator&[](thread Foo* foo, uint index)\n        {\n            if (index == 0)\n                return &foo->x;\n            if (index == 1)\n                return &foo->y;\n            return null;\n        }\n        int foo()\n        {\n            Foo foo;\n            foo[0] = 498;\n            foo[1] = 19;\n            return foo.x + foo.y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 498 + 19);
};
tests.overrideSubscriptStructAndUsePointers = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n            int y;\n        }\n        thread int* operator&[](thread Foo* foo, uint index)\n        {\n            if (index == 0)\n                return &foo->x;\n            if (index == 1)\n                return &foo->y;\n            return null;\n        }\n        int bar(thread Foo* foo)\n        {\n            return (*foo)[0] + (*foo)[1];\n        }\n        int foo()\n        {\n            Foo foo;\n            foo.x = 498;\n            foo.y = 19;\n            return bar(&foo);\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 498 + 19);
};
tests.overrideSubscriptStructAndUsePointersIncorrectly = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n                int y;\n            }\n            thread int* operator&[](thread Foo* foo, uint index)\n            {\n                if (index == 0)\n                    return &foo->x;\n                if (index == 1)\n                    return &foo->y;\n                return null;\n            }\n            int bar(thread Foo* foo)\n            {\n                return foo[0] + foo[1];\n            }\n            int foo()\n            {\n                Foo foo;\n                foo.x = 498;\n                foo.y = 19;\n                return bar(&foo);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.makeArrayRefFromLocal = function () {
  var program = doPrep("\n        int bar(thread int[] ref)\n        {\n            return ref[0];\n        }\n        int foo()\n        {\n            int x = 48;\n            return bar(@x);\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 48);
};
tests.makeArrayRefFromPointer = function () {
  var program = doPrep("\n        int bar(thread int[] ref)\n        {\n            return ref[0];\n        }\n        int baz(thread int* ptr)\n        {\n            return bar(@ptr);\n        }\n        int foo()\n        {\n            int x = 48;\n            return baz(&x);\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 48);
};
tests.makeArrayRefFromArrayRef = function () {
  checkFail(function () {
    return doPrep("\n            int bar(thread int[] ref)\n            {\n                return ref[0];\n            }\n            int baz(thread int[] ptr)\n            {\n                return bar(@ptr);\n            }\n            int foo()\n            {\n                int x = 48;\n                return baz(@x);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.simpleLength = function () {
  var program = doPrep("\n        uint foo()\n        {\n            double[754] array;\n            return (@array).length;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], []), 754);
};
tests.nonArrayRefArrayLengthSucceed = function () {
  var program = doPrep("\n        uint foo()\n        {\n            double[754] array;\n            return array.length;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], []), 754);
};
tests.nonArrayRefArrayLengthFail = function () {
  checkFail(function () {
    return doPrep("\n            thread uint* lengthPtr()\n            {\n                int[42] array;\n                return &(array.length);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.constexprIsNotLValuePtr = function () {
  checkFail(function () {
    return doPrep("\n            thread int* foo<int x>()\n            {\n                return &x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.constexprIsNotLValueAssign = function () {
  checkFail(function () {
    return doPrep("\n            void foo<int x>()\n            {\n                x = 42;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.constexprIsNotLValueRMW = function () {
  checkFail(function () {
    return doPrep("\n            void foo<int x>()\n            {\n                x += 42;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.assignLength = function () {
  checkFail(function () {
    return doPrep("\n            void foo()\n            {\n                double[754] array;\n                (@array).length = 42;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Have neither ander nor setter") != -1;
  });
};
tests.assignLengthHelper = function () {
  checkFail(function () {
    return doPrep("\n            void bar(thread double[] array)\n            {\n                array.length = 42;\n            }\n            void foo()\n            {\n                double[754] array;\n                bar(@array);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Have neither ander nor setter") != -1;
  });
};
tests.simpleGetter = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        int operator.y(Foo foo)\n        {\n            return foo.x;\n        }\n        int foo()\n        {\n            Foo foo;\n            foo.x = 7804;\n            return foo.y;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 7804);
};
tests.simpleSetter = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        int operator.y(Foo foo)\n        {\n            return foo.x;\n        }\n        Foo operator.y=(Foo foo, int value)\n        {\n            foo.x = value;\n            return foo;\n        }\n        int foo()\n        {\n            Foo foo;\n            foo.y = 7804;\n            return foo.x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 7804);
};
tests.genericAccessors = function () {
  var program = doPrep("\n        struct Foo<T> {\n            T x;\n            T[3] y;\n        }\n        struct Bar<T> {\n            T x;\n            T y;\n        }\n        Bar<T> operator.z<T>(Foo<T> foo)\n        {\n            Bar<T> result;\n            result.x = foo.x;\n            result.y = foo.y[1];\n            return result;\n        }\n        Foo<T> operator.z=<T>(Foo<T> foo, Bar<T> bar)\n        {\n            foo.x = bar.x;\n            foo.y[1] = bar.y;\n            return foo;\n        }\n        T operator.sum<T:Addable>(Foo<T> foo)\n        {\n            return foo.x + foo.y[0] + foo.y[1] + foo.y[2];\n        }\n        T operator.sum<T:Addable>(Bar<T> bar)\n        {\n            return bar.x + bar.y;\n        }\n        operator<T> Bar<T>(T x, T y)\n        {\n            Bar<T> result;\n            result.x = x;\n            result.y = y;\n            return result;\n        }\n        void setup(thread Foo<int>* foo)\n        {\n            foo->x = 1;\n            foo->y[0] = 2;\n            foo->y[1] = 3;\n            foo->y[2] = 4;\n        }\n        int testSuperBasic()\n        {\n            Foo<int> foo;\n            setup(&foo);\n            return foo.sum;\n        }\n        int testZSetterDidSetY()\n        {\n            Foo<int> foo;\n            foo.z = Bar<int>(53, 932);\n            return foo.y[1];\n        }\n        int testZSetter()\n        {\n            Foo<int> foo;\n            foo.z = Bar<int>(53, 932);\n            return foo.sum;\n        }\n        int testZGetter()\n        {\n            Foo<int> foo;\n            // This deliberately does not call setup() just so we test this syntax.\n            foo.x = 1;\n            foo.y[0] = 2;\n            foo.y[1] = 3;\n            foo.y[2] = 4;\n            return foo.z.sum;\n        }\n        int testLValueEmulation()\n        {\n            Foo<int> foo;\n            setup(&foo);\n            foo.z.y *= 5;\n            return foo.sum;\n        }\n    ");
  checkInt(program, callFunction(program, "testSuperBasic", [], []), 1 + 2 + 3 + 4);
  checkInt(program, callFunction(program, "testZSetterDidSetY", [], []), 932);
  checkInt(program, callFunction(program, "testZSetter", [], []), 53 + 932);
  checkInt(program, callFunction(program, "testZGetter", [], []), 1 + 3);
  checkInt(program, callFunction(program, "testLValueEmulation", [], []), 1 + 2 + 3 * 5 + 4);
};
tests.bitSubscriptAccessor = function () {
  var program = doPrep("\n        protocol MyBitmaskable : Equatable {\n            MyBitmaskable operator&(MyBitmaskable, MyBitmaskable);\n            MyBitmaskable operator|(MyBitmaskable, MyBitmaskable);\n            MyBitmaskable operator~(MyBitmaskable);\n            MyBitmaskable operator<<(MyBitmaskable, uint);\n            MyBitmaskable operator>>(MyBitmaskable, uint);\n            operator MyBitmaskable(int);\n        }\n        T maskForBitIndex<T:MyBitmaskable>(uint index)\n        {\n            return T(1) << index;\n        }\n        bool operator[]<T:MyBitmaskable>(T value, uint index)\n        {\n            return bool(value & maskForBitIndex<T>(index));\n        }\n        T operator[]=<T:MyBitmaskable>(T value, uint index, bool bit)\n        {\n            T mask = maskForBitIndex<T>(index);\n            if (bit)\n                value |= mask;\n            else\n                value &= ~mask;\n            return value;\n        }\n        uint operator.length(int)\n        {\n            return 32;\n        }\n        uint operator.length(uint)\n        {\n            return 32;\n        }\n        int testIntSetBit3()\n        {\n            int foo;\n            foo[3] = true;\n            return foo;\n        }\n        bool testIntSetGetBit5()\n        {\n            int foo;\n            foo[5] = true;\n            return foo[5];\n        }\n        bool testIntGetBit1()\n        {\n            int foo;\n            return foo[1];\n        }\n        int testUintSumBits()\n        {\n            int foo = 42;\n            int result;\n            for (uint i = 0; i < foo.length; ++i) {\n                if (foo[i])\n                    result++;\n            }\n            return result;\n        }\n        int testUintSwapBits()\n        {\n            int foo = 42;\n            for (uint i = 0; i < foo.length / 2; ++i) {\n                bool tmp = foo[i];\n                foo[i] = foo[foo.length - i - 1];\n                foo[foo.length - i - 1] = tmp;\n            }\n            return foo;\n        }\n        struct Foo {\n            uint f;\n            uint g;\n        }\n        operator Foo(uint f, uint g)\n        {\n            Foo result;\n            result.f = f;\n            result.g = g;\n            return result;\n        }\n        int operator.h(Foo foo)\n        {\n            return int((foo.f & 0xffff) | ((foo.g & 0xffff) << 16));\n        }\n        Foo operator.h=(Foo foo, int value)\n        {\n            foo.f &= ~0xffffu;\n            foo.f |= uint(value) & 0xffff;\n            foo.g &= ~0xffffu;\n            foo.g |= (uint(value) >> 16) & 0xffff;\n            return foo;\n        }\n        int testLValueEmulation()\n        {\n            Foo foo;\n            foo.f = 42;\n            foo.g = 37;\n            for (uint i = 0; i < foo.h.length; ++i)\n                foo.h[i] ^= true;\n            return int(foo.f + foo.g);\n        }\n        struct Bar {\n            Foo a;\n            Foo b;\n        }\n        Foo operator.c(Bar bar)\n        {\n            return Foo(uint(bar.a.h), uint(bar.b.h));\n        }\n        Bar operator.c=(Bar bar, Foo foo)\n        {\n            bar.a.h = int(foo.f);\n            bar.b.h = int(foo.g);\n            return bar;\n        }\n        int testCrazyLValueEmulation()\n        {\n            Bar bar;\n            bar.a.f = 1;\n            bar.a.g = 2;\n            bar.b.f = 3;\n            bar.b.g = 4;\n            for (uint i = 0; i < bar.c.h.length; i += 2)\n                bar.c.h[i] ^= true;\n            return int(bar.a.f + bar.a.g + bar.b.f + bar.b.g);\n        }\n    ");
  checkInt(program, callFunction(program, "testIntSetBit3", [], []), 8);
  checkBool(program, callFunction(program, "testIntSetGetBit5", [], []), true);
  checkBool(program, callFunction(program, "testIntGetBit1", [], []), false);
  checkInt(program, callFunction(program, "testUintSumBits", [], []), 3);
  checkInt(program, callFunction(program, "testUintSwapBits", [], []), 1409286144);
  checkInt(program, callFunction(program, "testLValueEmulation", [], []), 130991);
  checkInt(program, callFunction(program, "testCrazyLValueEmulation", [], []), 43696);
};
tests.nestedSubscriptLValueEmulationSimple = function () {
  var program = doPrep("\n        struct Foo {\n            int[7] array;\n        }\n        int operator[](Foo foo, uint index)\n        {\n            return foo.array[index];\n        }\n        Foo operator[]=(Foo foo, uint index, int value)\n        {\n            foo.array[index] = value;\n            return foo;\n        }\n        uint operator.length(Foo foo)\n        {\n            return foo.array.length;\n        }\n        int sum(Foo foo)\n        {\n            int result = 0;\n            for (uint i = foo.length; i--;)\n                result += foo[i];\n            return result;\n        }\n        struct Bar {\n            Foo[6] array;\n        }\n        uint operator.length(Bar bar)\n        {\n            return bar.array.length;\n        }\n        Foo operator[](Bar bar, uint index)\n        {\n            return bar.array[index];\n        }\n        Bar operator[]=(Bar bar, uint index, Foo value)\n        {\n            bar.array[index] = value;\n            return bar;\n        }\n        int sum(Bar bar)\n        {\n            int result = 0;\n            for (uint i = bar.length; i--;)\n                result += sum(bar[i]);\n            return result;\n        }\n        struct Baz {\n            Bar[5] array;\n        }\n        Bar operator[](Baz baz, uint index)\n        {\n            return baz.array[index];\n        }\n        Baz operator[]=(Baz baz, uint index, Bar value)\n        {\n            baz.array[index] = value;\n            return baz;\n        }\n        uint operator.length(Baz baz)\n        {\n            return baz.array.length;\n        }\n        int sum(Baz baz)\n        {\n            int result = 0;\n            for (uint i = baz.length; i--;)\n                result += sum(baz[i]);\n            return result;\n        }\n        void setValues(thread Baz* baz)\n        {\n            for (uint i = baz->length; i--;) {\n                for (uint j = (*baz)[i].length; j--;) {\n                    for (uint k = (*baz)[i][j].length; k--;)\n                        (*baz)[i][j][k] = int(i + j + k);\n                }\n            }\n        }\n        int testSetValuesAndSum()\n        {\n            Baz baz;\n            setValues(&baz);\n            return sum(baz);\n        }\n        int testSetValuesMutateValuesAndSum()\n        {\n            Baz baz;\n            setValues(&baz);\n            for (uint i = baz.length; i--;) {\n                for (uint j = baz[i].length; j--;) {\n                    for (uint k = baz[i][j].length; k--;)\n                        baz[i][j][k] *= int(k);\n                }\n            }\n            return sum(baz);\n        }\n    ");
  checkInt(program, callFunction(program, "testSetValuesAndSum", [], []), 1575);
  checkInt(program, callFunction(program, "testSetValuesMutateValuesAndSum", [], []), 5565);
};
tests.nestedSubscriptLValueEmulationGeneric = function () {
  var program = doPrep("\n        struct Foo<T> {\n            T[7] array;\n        }\n        T operator[]<T>(Foo<T> foo, uint index)\n        {\n            return foo.array[index];\n        }\n        Foo<T> operator[]=<T>(Foo<T> foo, uint index, T value)\n        {\n            foo.array[index] = value;\n            return foo;\n        }\n        uint operator.length<T>(Foo<T> foo)\n        {\n            return foo.array.length;\n        }\n        protocol MyAddable {\n            MyAddable operator+(MyAddable, MyAddable);\n        }\n        T sum<T:MyAddable>(Foo<T> foo)\n        {\n            T result;\n            for (uint i = foo.length; i--;)\n                result += foo[i];\n            return result;\n        }\n        struct Bar<T> {\n            Foo<T>[6] array;\n        }\n        uint operator.length<T>(Bar<T> bar)\n        {\n            return bar.array.length;\n        }\n        Foo<T> operator[]<T>(Bar<T> bar, uint index)\n        {\n            return bar.array[index];\n        }\n        Bar<T> operator[]=<T>(Bar<T> bar, uint index, Foo<T> value)\n        {\n            bar.array[index] = value;\n            return bar;\n        }\n        T sum<T:MyAddable>(Bar<T> bar)\n        {\n            T result;\n            for (uint i = bar.length; i--;)\n                result += sum(bar[i]);\n            return result;\n        }\n        struct Baz<T> {\n            Bar<T>[5] array;\n        }\n        Bar<T> operator[]<T>(Baz<T> baz, uint index)\n        {\n            return baz.array[index];\n        }\n        Baz<T> operator[]=<T>(Baz<T> baz, uint index, Bar<T> value)\n        {\n            baz.array[index] = value;\n            return baz;\n        }\n        uint operator.length<T>(Baz<T> baz)\n        {\n            return baz.array.length;\n        }\n        T sum<T:MyAddable>(Baz<T> baz)\n        {\n            T result;\n            for (uint i = baz.length; i--;)\n                result += sum(baz[i]);\n            return result;\n        }\n        protocol MyConvertibleFromUint {\n            operator MyConvertibleFromUint(uint);\n        }\n        protocol SetValuable : MyAddable, MyConvertibleFromUint { }\n        void setValues<T:SetValuable>(thread Baz<T>* baz)\n        {\n            for (uint i = baz->length; i--;) {\n                for (uint j = (*baz)[i].length; j--;) {\n                    for (uint k = (*baz)[i][j].length; k--;)\n                        (*baz)[i][j][k] = T(i + j + k);\n                }\n            }\n        }\n        int testSetValuesAndSum()\n        {\n            Baz<int> baz;\n            setValues(&baz);\n            return sum(baz);\n        }\n        int testSetValuesMutateValuesAndSum()\n        {\n            Baz<int> baz;\n            setValues(&baz);\n            for (uint i = baz.length; i--;) {\n                for (uint j = baz[i].length; j--;) {\n                    for (uint k = baz[i][j].length; k--;)\n                        baz[i][j][k] *= int(k);\n                }\n            }\n            return sum(baz);\n        }\n    ");
  checkInt(program, callFunction(program, "testSetValuesAndSum", [], []), 1575);
  checkInt(program, callFunction(program, "testSetValuesMutateValuesAndSum", [], []), 5565);
};
tests.boolBitAnd = function () {
  var program = doPrep("\n        bool foo(bool a, bool b)\n        {\n            return a & b;\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, false)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, false)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, true)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, true)]), true);
};
tests.boolBitOr = function () {
  var program = doPrep("\n        bool foo(bool a, bool b)\n        {\n            return a | b;\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, false)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, false)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, true)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, true)]), true);
};
tests.boolBitXor = function () {
  var program = doPrep("\n        bool foo(bool a, bool b)\n        {\n            return a ^ b;\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, false)]), false);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, false)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false), makeBool(program, true)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true), makeBool(program, true)]), false);
};
tests.boolBitNot = function () {
  var program = doPrep("\n        bool foo(bool a)\n        {\n            return ~a;\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, false)]), true);
  checkBool(program, callFunction(program, "foo", [], [makeBool(program, true)]), false);
};
tests.intBitAnd = function () {
  var program = doPrep("\n        int foo(int a, int b)\n        {\n            return a & b;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1), makeInt(program, 7)]), 1);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 65535), makeInt(program, 42)]), 42);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, -1), makeInt(program, -7)]), -7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0), makeInt(program, 85732)]), 0);
};
tests.intBitOr = function () {
  var program = doPrep("\n        int foo(int a, int b)\n        {\n            return a | b;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1), makeInt(program, 7)]), 7);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 65535), makeInt(program, 42)]), 65535);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, -1), makeInt(program, -7)]), -1);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0), makeInt(program, 85732)]), 85732);
};
tests.intBitXor = function () {
  var program = doPrep("\n        int foo(int a, int b)\n        {\n            return a ^ b;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1), makeInt(program, 7)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 65535), makeInt(program, 42)]), 65493);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, -1), makeInt(program, -7)]), 6);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0), makeInt(program, 85732)]), 85732);
};
tests.intBitNot = function () {
  var program = doPrep("\n        int foo(int a)\n        {\n            return ~a;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1)]), -2);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 65535)]), -65536);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, -1)]), 0);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0)]), -1);
};
tests.intLShift = function () {
  var program = doPrep("\n        int foo(int a, uint b)\n        {\n            return a << b;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1), makeUint(program, 7)]), 128);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 65535), makeUint(program, 2)]), 262140);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, -1), makeUint(program, 5)]), -32);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0), makeUint(program, 3)]), 0);
};
tests.intRShift = function () {
  var program = doPrep("\n        int foo(int a, uint b)\n        {\n            return a >> b;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 1), makeUint(program, 7)]), 0);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 65535), makeUint(program, 2)]), 16383);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, -1), makeUint(program, 5)]), -1);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0), makeUint(program, 3)]), 0);
};
tests.uintBitAnd = function () {
  var program = doPrep("\n        uint foo(uint a, uint b)\n        {\n            return a & b;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 1), makeUint(program, 7)]), 1);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 65535), makeUint(program, 42)]), 42);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, -1), makeUint(program, -7)]), 4294967289);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 0), makeUint(program, 85732)]), 0);
};
tests.uintBitOr = function () {
  var program = doPrep("\n        uint foo(uint a, uint b)\n        {\n            return a | b;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 1), makeUint(program, 7)]), 7);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 65535), makeUint(program, 42)]), 65535);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, -1), makeUint(program, -7)]), 4294967295);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 0), makeUint(program, 85732)]), 85732);
};
tests.uintBitXor = function () {
  var program = doPrep("\n        uint foo(uint a, uint b)\n        {\n            return a ^ b;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 1), makeUint(program, 7)]), 6);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 65535), makeUint(program, 42)]), 65493);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, -1), makeUint(program, -7)]), 6);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 0), makeUint(program, 85732)]), 85732);
};
tests.uintBitNot = function () {
  var program = doPrep("\n        uint foo(uint a)\n        {\n            return ~a;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 1)]), 4294967294);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 65535)]), 4294901760);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, -1)]), 0);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 0)]), 4294967295);
};
tests.uintLShift = function () {
  var program = doPrep("\n        uint foo(uint a, uint b)\n        {\n            return a << b;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 1), makeUint(program, 7)]), 128);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 65535), makeUint(program, 2)]), 262140);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, -1), makeUint(program, 5)]), 4294967264);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 0), makeUint(program, 3)]), 0);
};
tests.uintRShift = function () {
  var program = doPrep("\n        uint foo(uint a, uint b)\n        {\n            return a >> b;\n        }\n    ");
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 1), makeUint(program, 7)]), 0);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 65535), makeUint(program, 2)]), 16383);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, -1), makeUint(program, 5)]), 134217727);
  checkUint(program, callFunction(program, "foo", [], [makeUint(program, 0), makeUint(program, 3)]), 0);
};
tests.uint8BitAnd = function () {
  var program = doPrep("\n        uint8 foo(uint8 a, uint8 b)\n        {\n            return a & b;\n        }\n    ");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 1), makeUint8(program, 7)]), 1);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 65535), makeUint8(program, 42)]), 42);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, -1), makeUint8(program, -7)]), 249);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 0), makeUint8(program, 85732)]), 0);
};
tests.uint8BitOr = function () {
  var program = doPrep("\n        uint8 foo(uint8 a, uint8 b)\n        {\n            return a | b;\n        }\n    ");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 1), makeUint8(program, 7)]), 7);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 65535), makeUint8(program, 42)]), 255);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, -1), makeUint8(program, -7)]), 255);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 0), makeUint8(program, 85732)]), 228);
};
tests.uint8BitXor = function () {
  var program = doPrep("\n        uint8 foo(uint8 a, uint8 b)\n        {\n            return a ^ b;\n        }\n    ");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 1), makeUint8(program, 7)]), 6);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 65535), makeUint8(program, 42)]), 213);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, -1), makeUint8(program, -7)]), 6);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 0), makeUint8(program, 85732)]), 228);
};
tests.uint8BitNot = function () {
  var program = doPrep("\n        uint8 foo(uint8 a)\n        {\n            return ~a;\n        }\n    ");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 1)]), 254);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 65535)]), 0);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, -1)]), 0);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 0)]), 255);
};
tests.uint8LShift = function () {
  var program = doPrep("\n        uint8 foo(uint8 a, uint b)\n        {\n            return a << b;\n        }\n    ");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 1), makeUint(program, 7)]), 128);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 65535), makeUint(program, 2)]), 252);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, -1), makeUint(program, 5)]), 224);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 0), makeUint(program, 3)]), 0);
};
tests.uint8RShift = function () {
  var program = doPrep("\n        uint8 foo(uint8 a, uint b)\n        {\n            return a >> b;\n        }\n    ");
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 1), makeUint(program, 7)]), 0);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 65535), makeUint(program, 2)]), 255);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, -1), makeUint(program, 5)]), 255);
  checkUint8(program, callFunction(program, "foo", [], [makeUint8(program, 0), makeUint(program, 3)]), 0);
};
tests.floatMath = function () {
  var program = doPrep("\n        bool foo()\n        {\n            return 42.5 == 42.5;\n        }\n        bool foo2()\n        {\n            return 42.5f == 42.5;\n        }\n        bool foo3()\n        {\n            return 42.5 == 42.5f;\n        }\n        bool foo4()\n        {\n            return 42.5f == 42.5f;\n        }\n        bool foo5()\n        {\n            return 42.5d == 42.5d;\n        }\n        float bar(float x)\n        {\n            return x;\n        }\n        float foo6()\n        {\n            return bar(7.5);\n        }\n        float foo7()\n        {\n            return bar(7.5f);\n        }\n        float foo8()\n        {\n            return bar(7.5d);\n        }\n        float foo9()\n        {\n            return float(7.5);\n        }\n        float foo10()\n        {\n            return float(7.5f);\n        }\n        float foo11()\n        {\n            return float(7.5d);\n        }\n        float foo12()\n        {\n            return float(7);\n        }\n        float foo13()\n        {\n            double x = 7.5d;\n            return float(x);\n        }\n        double foo14()\n        {\n            double x = 7.5f;\n            return double(x);\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], []), true);
  checkBool(program, callFunction(program, "foo2", [], []), true);
  checkBool(program, callFunction(program, "foo3", [], []), true);
  checkBool(program, callFunction(program, "foo4", [], []), true);
  checkBool(program, callFunction(program, "foo5", [], []), true);
  checkFloat(program, callFunction(program, "foo6", [], []), 7.5);
  checkFloat(program, callFunction(program, "foo7", [], []), 7.5);
  checkFloat(program, callFunction(program, "foo8", [], []), 7.5);
  checkFloat(program, callFunction(program, "foo9", [], []), 7.5);
  checkFloat(program, callFunction(program, "foo10", [], []), 7.5);
  checkFloat(program, callFunction(program, "foo11", [], []), 7.5);
  checkFloat(program, callFunction(program, "foo12", [], []), 7);
  checkFloat(program, callFunction(program, "foo13", [], []), 7.5);
  checkDouble(program, callFunction(program, "foo14", [], []), 7.5);
  checkFail(function () {
    return doPrep("\n            int bar(int x)\n            {\n                return x;\n            }\n            int foo()\n            {\n                bar(4.);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int bar(int x)\n            {\n                return x;\n            }\n            int foo()\n            {\n                bar(4.d);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int bar(int x)\n            {\n                return x;\n            }\n            int foo()\n            {\n                bar(4.f);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            uint bar(uint x)\n            {\n                return x;\n            }\n            int foo()\n            {\n                bar(4.);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            uint bar(uint x)\n            {\n                return x;\n            }\n            int foo()\n            {\n                bar(4.d);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            uint bar(uint x)\n            {\n                return x;\n            }\n            int foo()\n            {\n                bar(4.f);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            float bar(float x)\n            {\n                return x;\n            }\n            void foo()\n            {\n                bar(16777217.d);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            float bar(float x)\n            {\n                return x;\n            }\n            float foo()\n            {\n                double x = 7.;\n                return bar(x);\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            float foo()\n            {\n                double x = 7.;\n                return x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.genericCastInfer = function () {
  var program = doPrep("\n        struct Complex<T> {\n            T real;\n            T imag;\n        }\n        operator<T> Complex<T>(T real, T imag)\n        {\n            Complex<T> result;\n            result.real = real;\n            result.imag = imag;\n            return result;\n        }\n        int foo()\n        {\n            Complex<int> x = Complex<int>(1, 2);\n            return x.real + x.imag;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 3);
};
tests.booleanMath = function () {
  var program = doPrep("\n        bool foo()\n        {\n            return true && true;\n        }\n        bool foo2()\n        {\n            return true && false;\n        }\n        bool foo3()\n        {\n            return false && true;\n        }\n        bool foo4()\n        {\n            return false && false;\n        }\n        bool foo5()\n        {\n            return true || true;\n        }\n        bool foo6()\n        {\n            return true || false;\n        }\n        bool foo7()\n        {\n            return false || true;\n        }\n        bool foo8()\n        {\n            return false || false;\n        }\n    ");
  checkBool(program, callFunction(program, "foo", [], []), true);
  checkBool(program, callFunction(program, "foo2", [], []), false);
  checkBool(program, callFunction(program, "foo3", [], []), false);
  checkBool(program, callFunction(program, "foo4", [], []), false);
  checkBool(program, callFunction(program, "foo5", [], []), true);
  checkBool(program, callFunction(program, "foo6", [], []), true);
  checkBool(program, callFunction(program, "foo7", [], []), true);
  checkBool(program, callFunction(program, "foo8", [], []), false);
};
tests.typedefArray = function () {
  var program = doPrep("\n        typedef ArrayTypedef = int[2];\n        int foo()\n        {\n            ArrayTypedef arrayTypedef;\n            return arrayTypedef[0];\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 0);
};
tests.shaderTypes = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                float4 x;\n            }\n            vertex Foo bar()\n            {\n                Foo result;\n                result.x = float4();\n                return result;\n            }\n            Foo foo() {\n                return bar();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            vertex float bar()\n            {\n                return 4.;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                float4 x;\n            }\n            vertex Foo bar(device Foo* x)\n            {\n                return Foo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Boo {\n                float4 x;\n            }\n            struct Foo {\n                float4 x;\n                device Boo* y;\n            }\n            vertex Foo bar()\n            {\n                return Foo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                float4 x;\n            }\n            struct Boo {\n                device Foo* y;\n            }\n            vertex Foo bar(Boo b)\n            {\n                return Foo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                float4 x;\n            }\n            vertex Foo bar(device Foo* x)\n            {\n                return Foo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                float4 x;\n            }\n            fragment Foo bar(Foo foo)\n            {\n                return Foo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                float4 x;\n            }\n            fragment Foo bar(device Foo* stageIn)\n            {\n                return Foo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Boo {\n                float4 x;\n            }\n            struct Foo {\n                float4 x;\n                device Boo* y;\n            }\n            fragment Boo bar(Foo stageIn)\n            {\n                return boo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Boo {\n                float4 x;\n            }\n            struct Foo {\n                float4 x;\n                device Boo* y;\n            }\n            fragment Foo bar(Boo stageIn)\n            {\n                return Foo();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.builtinVectors = function () {
  var program = doPrep("\n        int foo()\n        {\n            int2 a = int2(3, 4);\n            return a[0];\n        }\n        int foo2()\n        {\n            int2 a = int2(3, 4);\n            int3 b = int3(a, 5);\n            return b[1];\n        }\n        int foo3()\n        {\n            int3 a = int3(3, 4, 5);\n            int4 b = int4(6, a);\n            return b[1];\n        }\n        int foo4()\n        {\n            int2 a = int2(3, 4);\n            int2 b = int2(5, 6);\n            int4 c = int4(a, b);\n            return c[2];\n        }\n        bool foo5()\n        {\n            int4 a = int4(3, 4, 5, 6);\n            int2 b = int2(4, 5);\n            int4 c = int4(3, b, 6);\n            return a == c;\n        }\n        bool foo6()\n        {\n            int2 a = int2(4, 5);\n            int3 b = int3(3, a);\n            int3 c = int3(3, 4, 6);\n            return b == c;\n        }\n        uint foou()\n        {\n            uint2 a = uint2(3, 4);\n            return a[0];\n        }\n        uint foou2()\n        {\n            uint2 a = uint2(3, 4);\n            uint3 b = uint3(a, 5);\n            return b[1];\n        }\n        uint foou3()\n        {\n            uint3 a = uint3(3, 4, 5);\n            uint4 b = uint4(6, a);\n            return b[1];\n        }\n        uint foou4()\n        {\n            uint2 a = uint2(3, 4);\n            uint2 b = uint2(5, 6);\n            uint4 c = uint4(a, b);\n            return c[2];\n        }\n        bool foou5()\n        {\n            uint4 a = uint4(3, 4, 5, 6);\n            uint2 b = uint2(4, 5);\n            uint4 c = uint4(3, b, 6);\n            return a == c;\n        }\n        bool foou6()\n        {\n            uint2 a = uint2(4, 5);\n            uint3 b = uint3(3, a);\n            uint3 c = uint3(3, 4, 6);\n            return b == c;\n        }\n        float foof()\n        {\n            float2 a = float2(3., 4.);\n            return a[0];\n        }\n        float foof2()\n        {\n            float2 a = float2(3., 4.);\n            float3 b = float3(a, 5.);\n            return b[1];\n        }\n        float foof3()\n        {\n            float3 a = float3(3., 4., 5.);\n            float4 b = float4(6., a);\n            return b[1];\n        }\n        float foof4()\n        {\n            float2 a = float2(3., 4.);\n            float2 b = float2(5., 6.);\n            float4 c = float4(a, b);\n            return c[2];\n        }\n        bool foof5()\n        {\n            float4 a = float4(3., 4., 5., 6.);\n            float2 b = float2(4., 5.);\n            float4 c = float4(3., b, 6.);\n            return a == c;\n        }\n        bool foof6()\n        {\n            float2 a = float2(4., 5.);\n            float3 b = float3(3., a);\n            float3 c = float3(3., 4., 6.);\n            return b == c;\n        }\n        double food()\n        {\n            double2 a = double2(3., 4.);\n            return a[0];\n        }\n        double food2()\n        {\n            double2 a = double2(3., 4.);\n            double3 b = double3(a, 5.);\n            return b[1];\n        }\n        double food3()\n        {\n            double3 a = double3(3., 4., 5.);\n            double4 b = double4(6., a);\n            return b[1];\n        }\n        double food4()\n        {\n            double2 a = double2(3., 4.);\n            double2 b = double2(5., 6.);\n            double4 c = double4(a, b);\n            return c[2];\n        }\n        bool food5()\n        {\n            double4 a = double4(3., 4., 5., 6.);\n            double2 b = double2(4., 5.);\n            double4 c = double4(3., b, 6.);\n            return a == c;\n        }\n        bool food6()\n        {\n            double2 a = double2(4., 5.);\n            double3 b = double3(3., a);\n            double3 c = double3(3., 4., 6.);\n            return b == c;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 3);
  checkInt(program, callFunction(program, "foo2", [], []), 4);
  checkInt(program, callFunction(program, "foo3", [], []), 3);
  checkInt(program, callFunction(program, "foo4", [], []), 5);
  checkBool(program, callFunction(program, "foo5", [], []), true);
  checkBool(program, callFunction(program, "foo6", [], []), false);
  checkUint(program, callFunction(program, "foou", [], []), 3);
  checkUint(program, callFunction(program, "foou2", [], []), 4);
  checkUint(program, callFunction(program, "foou3", [], []), 3);
  checkUint(program, callFunction(program, "foou4", [], []), 5);
  checkBool(program, callFunction(program, "foou5", [], []), true);
  checkBool(program, callFunction(program, "foou6", [], []), false);
  checkFloat(program, callFunction(program, "foof", [], []), 3);
  checkFloat(program, callFunction(program, "foof2", [], []), 4);
  checkFloat(program, callFunction(program, "foof3", [], []), 3);
  checkFloat(program, callFunction(program, "foof4", [], []), 5);
  checkBool(program, callFunction(program, "foof5", [], []), true);
  checkBool(program, callFunction(program, "foof6", [], []), false);
  checkDouble(program, callFunction(program, "food", [], []), 3);
  checkDouble(program, callFunction(program, "food2", [], []), 4);
  checkDouble(program, callFunction(program, "food3", [], []), 3);
  checkDouble(program, callFunction(program, "food4", [], []), 5);
  checkBool(program, callFunction(program, "food5", [], []), true);
  checkBool(program, callFunction(program, "food6", [], []), false);
};
tests.instantiateStructInStruct = function () {
  var program = doPrep("\n        struct Bar<T> {\n            T x;\n        }\n        struct Foo {\n            Bar<int> x;\n        }\n        int foo()\n        {\n            Foo x;\n            x.x.x = 42;\n            x.x.x++;\n            return x.x.x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 43);
};
tests.instantiateStructInStructWithInt2 = function () {
  var program = doPrep("\n        struct Foo {\n            int2 x;\n        }\n        int foo()\n        {\n            Foo x;\n            x.x.x = 42;\n            x.x.x++;\n            return x.x.x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 43);
};
tests.simpleEnum = function () {
  var program = doPrep("\n        enum Foo {\n            War,\n            Famine,\n            Pestilence,\n            Death\n        }\n        Foo war()\n        {\n            return Foo.War;\n        }\n        Foo famine()\n        {\n            return Foo.Famine;\n        }\n        Foo pestilence()\n        {\n            return Foo.Pestilence;\n        }\n        Foo death()\n        {\n            return Foo.Death;\n        }\n        bool equals(Foo a, Foo b)\n        {\n            return a == b;\n        }\n        bool notEquals(Foo a, Foo b)\n        {\n            return a != b;\n        }\n        bool testSimpleEqual()\n        {\n            return equals(Foo.War, Foo.War);\n        }\n        bool testAnotherEqual()\n        {\n            return equals(Foo.Pestilence, Foo.Pestilence);\n        }\n        bool testNotEqual()\n        {\n            return equals(Foo.Famine, Foo.Death);\n        }\n        bool testSimpleNotEqual()\n        {\n            return notEquals(Foo.War, Foo.War);\n        }\n        bool testAnotherNotEqual()\n        {\n            return notEquals(Foo.Pestilence, Foo.Pestilence);\n        }\n        bool testNotNotEqual()\n        {\n            return notEquals(Foo.Famine, Foo.Death);\n        }\n        int intWar()\n        {\n            return int(war());\n        }\n        int intFamine()\n        {\n            return int(famine());\n        }\n        int intPestilence()\n        {\n            return int(pestilence());\n        }\n        int intDeath()\n        {\n            return int(death());\n        }\n        int warValue()\n        {\n            return war().value;\n        }\n        int famineValue()\n        {\n            return famine().value;\n        }\n        int pestilenceValue()\n        {\n            return pestilence().value;\n        }\n        int deathValue()\n        {\n            return death().value;\n        }\n        int warValueLiteral()\n        {\n            return Foo.War.value;\n        }\n        int famineValueLiteral()\n        {\n            return Foo.Famine.value;\n        }\n        int pestilenceValueLiteral()\n        {\n            return Foo.Pestilence.value;\n        }\n        int deathValueLiteral()\n        {\n            return Foo.Death.value;\n        }\n        Foo intWarBackwards()\n        {\n            return Foo(intWar());\n        }\n        Foo intFamineBackwards()\n        {\n            return Foo(intFamine());\n        }\n        Foo intPestilenceBackwards()\n        {\n            return Foo(intPestilence());\n        }\n        Foo intDeathBackwards()\n        {\n            return Foo(intDeath());\n        }\n    ");
  checkEnum(program, callFunction(program, "war", [], []), 0);
  checkEnum(program, callFunction(program, "famine", [], []), 1);
  checkEnum(program, callFunction(program, "pestilence", [], []), 2);
  checkEnum(program, callFunction(program, "death", [], []), 3);
  checkBool(program, callFunction(program, "testSimpleEqual", [], []), true);
  checkBool(program, callFunction(program, "testAnotherEqual", [], []), true);
  checkBool(program, callFunction(program, "testNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testSimpleNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testAnotherNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testNotNotEqual", [], []), true);
  checkInt(program, callFunction(program, "intWar", [], []), 0);
  checkInt(program, callFunction(program, "intFamine", [], []), 1);
  checkInt(program, callFunction(program, "intPestilence", [], []), 2);
  checkInt(program, callFunction(program, "intDeath", [], []), 3);
  checkInt(program, callFunction(program, "warValue", [], []), 0);
  checkInt(program, callFunction(program, "famineValue", [], []), 1);
  checkInt(program, callFunction(program, "pestilenceValue", [], []), 2);
  checkInt(program, callFunction(program, "deathValue", [], []), 3);
  checkInt(program, callFunction(program, "warValueLiteral", [], []), 0);
  checkInt(program, callFunction(program, "famineValueLiteral", [], []), 1);
  checkInt(program, callFunction(program, "pestilenceValueLiteral", [], []), 2);
  checkInt(program, callFunction(program, "deathValueLiteral", [], []), 3);
  checkEnum(program, callFunction(program, "intWarBackwards", [], []), 0);
  checkEnum(program, callFunction(program, "intFamineBackwards", [], []), 1);
  checkEnum(program, callFunction(program, "intPestilenceBackwards", [], []), 2);
  checkEnum(program, callFunction(program, "intDeathBackwards", [], []), 3);
};
tests.enumWithManualValues = function () {
  var program = doPrep("\n        enum Foo {\n            War = 72,\n            Famine = 0,\n            Pestilence = 23,\n            Death = -42\n        }\n        Foo war()\n        {\n            return Foo.War;\n        }\n        Foo famine()\n        {\n            return Foo.Famine;\n        }\n        Foo pestilence()\n        {\n            return Foo.Pestilence;\n        }\n        Foo death()\n        {\n            return Foo.Death;\n        }\n    ");
  checkEnum(program, callFunction(program, "war", [], []), 72);
  checkEnum(program, callFunction(program, "famine", [], []), 0);
  checkEnum(program, callFunction(program, "pestilence", [], []), 23);
  checkEnum(program, callFunction(program, "death", [], []), -42);
};
tests.enumWithoutZero = function () {
  checkFail(function () {
    return doPrep("\n            enum Foo {\n                War = 72,\n                Famine = 64,\n                Pestilence = 23,\n                Death = -42\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.enumDuplicates = function () {
  checkFail(function () {
    return doPrep("\n            enum Foo {\n                War = -42,\n                Famine = 0,\n                Pestilence = 23,\n                Death = -42\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.enumWithSomeManualValues = function () {
  var program = doPrep("\n        enum Foo {\n            War = 72,\n            Famine,\n            Pestilence = 0,\n            Death\n        }\n        Foo war()\n        {\n            return Foo.War;\n        }\n        Foo famine()\n        {\n            return Foo.Famine;\n        }\n        Foo pestilence()\n        {\n            return Foo.Pestilence;\n        }\n        Foo death()\n        {\n            return Foo.Death;\n        }\n    ");
  checkEnum(program, callFunction(program, "war", [], []), 72);
  checkEnum(program, callFunction(program, "famine", [], []), 73);
  checkEnum(program, callFunction(program, "pestilence", [], []), 0);
  checkEnum(program, callFunction(program, "death", [], []), 1);
};
tests.enumConstexprGenericFunction = function () {
  var program = doPrep("\n        enum Axis { X, Y }\n        int foo<Axis axis>() { return int(axis); }\n        int testX() { return foo<Axis.X>(); }\n        int testY() { return foo<Axis.Y>(); }\n    ");
  checkInt(program, callFunction(program, "testX", [], []), 0);
  checkInt(program, callFunction(program, "testY", [], []), 1);
};
tests.enumConstexprGenericStruct = function () {
  var program = doPrep("\n        enum Axis { X, Y }\n        struct Foo<Axis axis> { }\n        int foo<Axis axis>(Foo<axis>) { return int(axis); }\n        int testX()\n        {   \n            Foo<Axis.X> f;\n            return foo(f);\n        }\n        int testY()\n        {   \n            Foo<Axis.Y> f;\n            return foo(f);\n        }\n    ");
  checkInt(program, callFunction(program, "testX", [], []), 0);
  checkInt(program, callFunction(program, "testY", [], []), 1);
};
tests.trap = function () {
  var program = doPrep("\n        int foo()\n        {\n            trap;\n        }\n        int foo2(int x)\n        {\n            if (x == 3)\n                trap;\n            return 4;\n        }\n        struct Bar {\n            int3 x;\n            float y;\n        }\n        Bar foo3()\n        {\n            trap;\n        }\n    ");
  checkFail(function () {
    return callFunction(program, "foo", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
  checkInt(program, callFunction(program, "foo2", [], [makeInt(program, 1)]), 4);
  checkFail(function () {
    return callFunction(program, "foo2", [], [makeInt(program, 3)]);
  }, function (e) {
    return e instanceof WTrapError;
  });
  checkFail(function () {
    return callFunction(program, "foo3", [], []);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.swizzle = function () {
  var program = doPrep("\n        float foo() {\n            float4 bar = float4(3., 4., 5., 6.);\n            float3 baz = bar.zzx;\n            return baz.z;\n        }\n        float foo2() {\n            float4 bar = float4(3., 4., 5., 6.);\n            float3 baz = bar.wyz;\n            return baz.x;\n        }\n        float foo3() {\n            float3 bar = float3(3., 4., 5.);\n            float2 baz = bar.yz;\n            float4 quix = baz.yyxx;\n            return quix.z;\n        }\n    ");
  checkFloat(program, callFunction(program, "foo", [], []), 3);
  checkFloat(program, callFunction(program, "foo2", [], []), 6);
  checkFloat(program, callFunction(program, "foo3", [], []), 4);
};
tests.enumWithExplicitIntBase = function () {
  var program = doPrep("\n        enum Foo : int {\n            War,\n            Famine,\n            Pestilence,\n            Death\n        }\n        Foo war()\n        {\n            return Foo.War;\n        }\n        Foo famine()\n        {\n            return Foo.Famine;\n        }\n        Foo pestilence()\n        {\n            return Foo.Pestilence;\n        }\n        Foo death()\n        {\n            return Foo.Death;\n        }\n        bool equals(Foo a, Foo b)\n        {\n            return a == b;\n        }\n        bool notEquals(Foo a, Foo b)\n        {\n            return a != b;\n        }\n        bool testSimpleEqual()\n        {\n            return equals(Foo.War, Foo.War);\n        }\n        bool testAnotherEqual()\n        {\n            return equals(Foo.Pestilence, Foo.Pestilence);\n        }\n        bool testNotEqual()\n        {\n            return equals(Foo.Famine, Foo.Death);\n        }\n        bool testSimpleNotEqual()\n        {\n            return notEquals(Foo.War, Foo.War);\n        }\n        bool testAnotherNotEqual()\n        {\n            return notEquals(Foo.Pestilence, Foo.Pestilence);\n        }\n        bool testNotNotEqual()\n        {\n            return notEquals(Foo.Famine, Foo.Death);\n        }\n        int intWar()\n        {\n            return int(war());\n        }\n        int intFamine()\n        {\n            return int(famine());\n        }\n        int intPestilence()\n        {\n            return int(pestilence());\n        }\n        int intDeath()\n        {\n            return int(death());\n        }\n        int warValue()\n        {\n            return war().value;\n        }\n        int famineValue()\n        {\n            return famine().value;\n        }\n        int pestilenceValue()\n        {\n            return pestilence().value;\n        }\n        int deathValue()\n        {\n            return death().value;\n        }\n        int warValueLiteral()\n        {\n            return Foo.War.value;\n        }\n        int famineValueLiteral()\n        {\n            return Foo.Famine.value;\n        }\n        int pestilenceValueLiteral()\n        {\n            return Foo.Pestilence.value;\n        }\n        int deathValueLiteral()\n        {\n            return Foo.Death.value;\n        }\n        Foo intWarBackwards()\n        {\n            return Foo(intWar());\n        }\n        Foo intFamineBackwards()\n        {\n            return Foo(intFamine());\n        }\n        Foo intPestilenceBackwards()\n        {\n            return Foo(intPestilence());\n        }\n        Foo intDeathBackwards()\n        {\n            return Foo(intDeath());\n        }\n    ");
  checkEnum(program, callFunction(program, "war", [], []), 0);
  checkEnum(program, callFunction(program, "famine", [], []), 1);
  checkEnum(program, callFunction(program, "pestilence", [], []), 2);
  checkEnum(program, callFunction(program, "death", [], []), 3);
  checkBool(program, callFunction(program, "testSimpleEqual", [], []), true);
  checkBool(program, callFunction(program, "testAnotherEqual", [], []), true);
  checkBool(program, callFunction(program, "testNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testSimpleNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testAnotherNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testNotNotEqual", [], []), true);
  checkInt(program, callFunction(program, "intWar", [], []), 0);
  checkInt(program, callFunction(program, "intFamine", [], []), 1);
  checkInt(program, callFunction(program, "intPestilence", [], []), 2);
  checkInt(program, callFunction(program, "intDeath", [], []), 3);
  checkInt(program, callFunction(program, "warValue", [], []), 0);
  checkInt(program, callFunction(program, "famineValue", [], []), 1);
  checkInt(program, callFunction(program, "pestilenceValue", [], []), 2);
  checkInt(program, callFunction(program, "deathValue", [], []), 3);
  checkInt(program, callFunction(program, "warValueLiteral", [], []), 0);
  checkInt(program, callFunction(program, "famineValueLiteral", [], []), 1);
  checkInt(program, callFunction(program, "pestilenceValueLiteral", [], []), 2);
  checkInt(program, callFunction(program, "deathValueLiteral", [], []), 3);
  checkEnum(program, callFunction(program, "intWarBackwards", [], []), 0);
  checkEnum(program, callFunction(program, "intFamineBackwards", [], []), 1);
  checkEnum(program, callFunction(program, "intPestilenceBackwards", [], []), 2);
  checkEnum(program, callFunction(program, "intDeathBackwards", [], []), 3);
};
tests.enumWithUintBase = function () {
  var program = doPrep("\n        enum Foo : uint {\n            War,\n            Famine,\n            Pestilence,\n            Death\n        }\n        Foo war()\n        {\n            return Foo.War;\n        }\n        Foo famine()\n        {\n            return Foo.Famine;\n        }\n        Foo pestilence()\n        {\n            return Foo.Pestilence;\n        }\n        Foo death()\n        {\n            return Foo.Death;\n        }\n        bool equals(Foo a, Foo b)\n        {\n            return a == b;\n        }\n        bool notEquals(Foo a, Foo b)\n        {\n            return a != b;\n        }\n        bool testSimpleEqual()\n        {\n            return equals(Foo.War, Foo.War);\n        }\n        bool testAnotherEqual()\n        {\n            return equals(Foo.Pestilence, Foo.Pestilence);\n        }\n        bool testNotEqual()\n        {\n            return equals(Foo.Famine, Foo.Death);\n        }\n        bool testSimpleNotEqual()\n        {\n            return notEquals(Foo.War, Foo.War);\n        }\n        bool testAnotherNotEqual()\n        {\n            return notEquals(Foo.Pestilence, Foo.Pestilence);\n        }\n        bool testNotNotEqual()\n        {\n            return notEquals(Foo.Famine, Foo.Death);\n        }\n        uint uintWar()\n        {\n            return uint(war());\n        }\n        uint uintFamine()\n        {\n            return uint(famine());\n        }\n        uint uintPestilence()\n        {\n            return uint(pestilence());\n        }\n        uint uintDeath()\n        {\n            return uint(death());\n        }\n        uint warValue()\n        {\n            return war().value;\n        }\n        uint famineValue()\n        {\n            return famine().value;\n        }\n        uint pestilenceValue()\n        {\n            return pestilence().value;\n        }\n        uint deathValue()\n        {\n            return death().value;\n        }\n        uint warValueLiteral()\n        {\n            return Foo.War.value;\n        }\n        uint famineValueLiteral()\n        {\n            return Foo.Famine.value;\n        }\n        uint pestilenceValueLiteral()\n        {\n            return Foo.Pestilence.value;\n        }\n        uint deathValueLiteral()\n        {\n            return Foo.Death.value;\n        }\n        Foo uintWarBackwards()\n        {\n            return Foo(uintWar());\n        }\n        Foo uintFamineBackwards()\n        {\n            return Foo(uintFamine());\n        }\n        Foo uintPestilenceBackwards()\n        {\n            return Foo(uintPestilence());\n        }\n        Foo uintDeathBackwards()\n        {\n            return Foo(uintDeath());\n        }\n    ");
  checkEnum(program, callFunction(program, "war", [], []), 0);
  checkEnum(program, callFunction(program, "famine", [], []), 1);
  checkEnum(program, callFunction(program, "pestilence", [], []), 2);
  checkEnum(program, callFunction(program, "death", [], []), 3);
  checkBool(program, callFunction(program, "testSimpleEqual", [], []), true);
  checkBool(program, callFunction(program, "testAnotherEqual", [], []), true);
  checkBool(program, callFunction(program, "testNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testSimpleNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testAnotherNotEqual", [], []), false);
  checkBool(program, callFunction(program, "testNotNotEqual", [], []), true);
  checkUint(program, callFunction(program, "uintWar", [], []), 0);
  checkUint(program, callFunction(program, "uintFamine", [], []), 1);
  checkUint(program, callFunction(program, "uintPestilence", [], []), 2);
  checkUint(program, callFunction(program, "uintDeath", [], []), 3);
  checkUint(program, callFunction(program, "warValue", [], []), 0);
  checkUint(program, callFunction(program, "famineValue", [], []), 1);
  checkUint(program, callFunction(program, "pestilenceValue", [], []), 2);
  checkUint(program, callFunction(program, "deathValue", [], []), 3);
  checkUint(program, callFunction(program, "warValueLiteral", [], []), 0);
  checkUint(program, callFunction(program, "famineValueLiteral", [], []), 1);
  checkUint(program, callFunction(program, "pestilenceValueLiteral", [], []), 2);
  checkUint(program, callFunction(program, "deathValueLiteral", [], []), 3);
  checkEnum(program, callFunction(program, "uintWarBackwards", [], []), 0);
  checkEnum(program, callFunction(program, "uintFamineBackwards", [], []), 1);
  checkEnum(program, callFunction(program, "uintPestilenceBackwards", [], []), 2);
  checkEnum(program, callFunction(program, "uintDeathBackwards", [], []), 3);
};
tests.enumFloatBase = function () {
  checkFail(function () {
    return doPrep("\n            enum Foo : float {\n                Bar\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.enumPtrBase = function () {
  checkFail(function () {
    return doPrep("\n            enum Foo : thread int* {\n                Bar\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.enumArrayRefBase = function () {
  checkFail(function () {
    return doPrep("\n            enum Foo : thread int[] {\n                Bar\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.emptyStruct = function () {
  var program = doPrep("\n        struct Thingy { }\n        int foo()\n        {\n            Thingy thingy;\n            return 46;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 46);
};
tests.enumStructBase = function () {
  checkFail(function () {
    return doPrep("\n            struct Thingy { }\n            enum Foo : Thingy {\n                Bar\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.enumNoMembers = function () {
  checkFail(function () {
    return doPrep("\n            enum Foo { }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.simpleSwitch = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            switch (x) {\n            case 767:\n                return 27;\n            case 69:\n                return 7624;\n            default:\n                return 49;\n            }\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 767)]), 27);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 69)]), 7624);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0)]), 49);
};
tests.exhaustiveUint8Switch = function () {
  var text = "double foo(uint8 x) { switch (uint8(x)) {";
  for (var i = 0; i <= 0xff; ++i) text += "case " + i + ": return " + i * 1.5 + ";";
  text += "} }";
  var program = doPrep(text);
  for (var _i = 0; _i < 0xff; ++_i) checkDouble(program, callFunction(program, "foo", [], [makeUint8(program, _i)]), _i * 1.5);
};
tests.notQuiteExhaustiveUint8Switch = function () {
  var text = "double foo(uint8 x) { switch (uint8(x)) {";
  for (var i = 0; i <= 0xfe; ++i) text += "case " + i + ": return " + i * 1.5 + ";";
  text += "} }";
  checkFail(function () {
    return doPrep(text);
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.notQuiteExhaustiveUint8SwitchWithDefault = function () {
  var text = "double foo(uint8 x) { switch (uint8(x)) {";
  for (var i = 0; i <= 0xfe; ++i) text += "case " + i + ": return " + i * 1.5 + ";";
  text += "default: return " + 0xff * 1.5 + ";";
  text += "} }";
  var program = doPrep(text);
  for (var _i2 = 0; _i2 < 0xff; ++_i2) checkDouble(program, callFunction(program, "foo", [], [makeUint8(program, _i2)]), _i2 * 1.5);
};
tests.switchFallThrough = function () {
  // FIXME: This might become an error in future versions.
  // https://bugs.webkit.org/show_bug.cgi?id=177172
  var program = doPrep("\n        int foo(int x)\n        {\n            int result = 0;\n            switch (x) {\n            case 767:\n                result += 27;\n            case 69:\n                result += 7624;\n            default:\n                result += 49;\n            }\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 767)]), 27 + 7624 + 49);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 69)]), 7624 + 49);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0)]), 49);
};
tests.switchBreak = function () {
  var program = doPrep("\n        int foo(int x)\n        {\n            int result = 0;\n            switch (x) {\n            case 767:\n                result += 27;\n                break;\n            case 69:\n                result += 7624;\n                break;\n            default:\n                result += 49;\n                break;\n            }\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 767)]), 27);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 69)]), 7624);
  checkInt(program, callFunction(program, "foo", [], [makeInt(program, 0)]), 49);
};
tests.enumSwitchBreakExhaustive = function () {
  var program = doPrep("\n        enum Foo {\n            A, B, C\n        }\n        int foo(Foo x)\n        {\n            int result = 0;\n            switch (x) {\n            case Foo.A:\n                result += 27;\n                break;\n            case Foo.B:\n                result += 7624;\n                break;\n            case Foo.C:\n                result += 49;\n                break;\n            }\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeEnum(program, "Foo", "A")]), 27);
  checkInt(program, callFunction(program, "foo", [], [makeEnum(program, "Foo", "B")]), 7624);
  checkInt(program, callFunction(program, "foo", [], [makeEnum(program, "Foo", "C")]), 49);
};
tests.enumSwitchBreakNotQuiteExhaustive = function () {
  checkFail(function () {
    return doPrep("\n            enum Foo {\n                A, B, C, D\n            }\n            int foo(Foo x)\n            {\n                int result = 0;\n                switch (x) {\n                case Foo.A:\n                    result += 27;\n                    break;\n                case Foo.B:\n                    result += 7624;\n                    break;\n                case Foo.C:\n                    result += 49;\n                    break;\n                }\n                return result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.enumSwitchBreakNotQuiteExhaustiveWithDefault = function () {
  var program = doPrep("\n        enum Foo {\n            A, B, C\n        }\n        int foo(Foo x)\n        {\n            int result = 0;\n            switch (x) {\n            case Foo.A:\n                result += 27;\n                break;\n            case Foo.B:\n                result += 7624;\n                break;\n            default:\n                result += 49;\n                break;\n            }\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], [makeEnum(program, "Foo", "A")]), 27);
  checkInt(program, callFunction(program, "foo", [], [makeEnum(program, "Foo", "B")]), 7624);
  checkInt(program, callFunction(program, "foo", [], [makeEnum(program, "Foo", "C")]), 49);
};
tests.simpleRecursiveStruct = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                Foo foo;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.mutuallyRecursiveStruct = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                Bar bar;\n            }\n            struct Bar {\n                Foo foo;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.mutuallyRecursiveStructWithPointersBroken = function () {
  var program = doPrep("\n        struct Foo {\n            thread Bar* bar;\n            int foo;\n        }\n        struct Bar {\n            thread Foo* foo;\n            int bar;\n        }\n        int foo()\n        {\n            Foo foo;\n            Bar bar;\n            foo.foo = 564;\n            bar.bar = 53;\n            return foo.bar->bar - bar.foo->foo;\n        }\n    ");
  checkFail(function () {
    return checkInt(program, callFunction(program, "foo", [], []), -511);
  }, function (e) {
    return e instanceof WTrapError;
  });
};
tests.mutuallyRecursiveStructWithPointers = function () {
  var program = doPrep("\n        struct Foo {\n            thread Bar* bar;\n            int foo;\n        }\n        struct Bar {\n            thread Foo* foo;\n            int bar;\n        }\n        int foo()\n        {\n            Foo foo;\n            Bar bar;\n            foo.bar = &bar;\n            bar.foo = &foo;\n            foo.foo = 564;\n            bar.bar = 53;\n            return foo.bar->bar - bar.foo->foo;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), -511);
};
tests.linkedList = function () {
  var program = doPrep("\n        struct Node {\n            thread Node* next;\n            int value;\n        }\n        int foo()\n        {\n            Node x, y, z;\n            x.next = &y;\n            y.next = &z;\n            x.value = 1;\n            y.value = 2;\n            z.value = 3;\n            return x.next->next->value;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 3);
};
tests.pointerToPointer = function () {
  var program = doPrep("\n        int foo()\n        {\n            int x;\n            thread int* p = &x;\n            thread int** pp = &p;\n            int*thread*thread qq = pp;\n            int result = 0;\n            x = 42;\n            *p = 76;\n            result += x;\n            **pp = 39;\n            result += x;\n            **qq = 83;\n            result += x;\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 76 + 39 + 83);
};
tests.arrayRefToArrayRef = function () {
  var program = doPrep("\n        int foo()\n        {\n            int x;\n            thread int[] p = @x;\n            thread int[][] pp = @p;\n            int[]thread[]thread qq = pp;\n            int result = 0;\n            x = 42;\n            p[0] = 76;\n            result += x;\n            pp[0][0] = 39;\n            result += x;\n            qq[0][0] = 83;\n            result += x;\n            return result;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 76 + 39 + 83);
};
tests.pointerGetter = function () {
  checkFail(function () {
    return doPrep("\n            int operator.foo(device int*)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator.foo(thread int*)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator.foo(threadgroup int*)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator.foo(constant int*)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.loneSetter = function () {
  checkFail(function () {
    return doPrep("\n            int operator.foo=(int, int)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.setterWithMismatchedType = function () {
  checkFail(function () {
    return doPrep("\n            double operator.foo(int)\n            {\n                return 5.43;\n            }\n            int operator.foo=(int, int)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.setterWithMatchedType = function () {
  doPrep("\n        int operator.foo(int)\n        {\n            return 5;\n        }\n        int operator.foo=(int, int)\n        {\n            return 543;\n        }\n    ");
};
tests.operatorWithUninferrableTypeVariable = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            Foo operator+<T>(Foo a, Foo b)\n            {\n                Foo result;\n                result.x = a.x + b.x;\n                return result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.operatorWithoutUninferrableTypeVariable = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        Foo operator+(Foo a, Foo b)\n        {\n            Foo result;\n            result.x = a.x + b.x;\n            return result;\n        }\n        int foo()\n        {\n            Foo a;\n            a.x = 645;\n            Foo b;\n            b.x = -35;\n            return (a + b).x;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 645 - 35);
};
tests.operatorCastWithUninferrableTypeVariable = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            operator<T> Foo(int x)\n            {\n                Foo result;\n                result.x = x;\n                return result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.operatorCastWithTypeVariableInferredFromReturnType = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        protocol Barable {\n            void bar(thread Barable*, int);\n        }\n        void bar(thread double* result, int value)\n        {\n            *result = double(value);\n        }\n        operator<T:Barable> T(Foo foo)\n        {\n            T result;\n            bar(&result, foo.x);\n            return result;\n        }\n        int foo()\n        {\n            Foo foo;\n            foo.x = 75;\n            double x = double(foo);\n            return int(x * 1.5);\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 112);
};
tests.incWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator++() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator++(int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.decWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator--() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator--(int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.incWrongTypes = function () {
  checkFail(function () {
    return doPrep("\n            int operator++(double) { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.decWrongTypes = function () {
  checkFail(function () {
    return doPrep("\n            int operator--(double) { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.plusWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator+() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator+(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.minusWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator-() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator-(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.timesWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator*() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator*(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator*(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.divideWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator/() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator/(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator/(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.moduloWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator%() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator%(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator%(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.bitAndWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator&() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator&(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator&(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.bitOrWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator|() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator|(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator|(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.bitXorWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator^() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator^(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator^(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.lShiftWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator<<() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator<<(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator<<(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.rShiftWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator>>() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator>>(int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator>>(int, int, int) { return 76; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.bitNotWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator~() { return 32; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator~(int, int) { return 534; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.equalsWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            bool operator==() { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator==(int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator==(int, int, int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.lessThanWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            bool operator<() { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator<(int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator<(int, int, int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.lessEqualWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            bool operator<=() { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator<=(int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator<=(int, int, int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.greaterWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            bool operator>() { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator>(int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator>(int, int, int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.greaterEqualWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            bool operator>=() { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator>=(int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            bool operator>=(int, int, int) { return true; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.equalsWrongReturnType = function () {
  checkFail(function () {
    return doPrep("\n            int operator==(int a, int b) { return a + b; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.notEqualsOverload = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo { }\n            bool operator!=(Foo, Foo) { return true; }\n        ");
  }, function (e) {
    return e instanceof WSyntaxError;
  });
};
tests.lessThanWrongReturnType = function () {
  checkFail(function () {
    return doPrep("\n            int operator<(int a, int b) { return a + b; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.lessEqualWrongReturnType = function () {
  checkFail(function () {
    return doPrep("\n            int operator<=(int a, int b) { return a + b; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.greaterThanWrongReturnType = function () {
  checkFail(function () {
    return doPrep("\n            int operator>(int a, int b) { return a + b; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.greaterEqualWrongReturnType = function () {
  checkFail(function () {
    return doPrep("\n            int operator>=(int a, int b) { return a + b; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.dotOperatorWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator.foo() { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo { }\n            int operator.foo(Foo, int) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.dotOperatorSetterWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo { }\n            Foo operator.foo=() { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo { }\n            Foo operator.foo=(Foo) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo { }\n            Foo operator.foo=(Foo, int, int) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.loneSetterPointer = function () {
  checkFail(function () {
    return doPrep("\n            thread int* operator.foo=(thread int* ptr, int)\n            {\n                return ptr;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.setterWithNoGetterOverload = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo { }\n            struct Bar { }\n            int operator.foo(Foo)\n            {\n                return 534;\n            }\n            Bar operator.foo=(Bar, int)\n            {\n                return Bar();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.setterWithNoGetterOverloadFixed = function () {
  doPrep("\n        struct Bar { }\n        int operator.foo(Bar)\n        {\n            return 534;\n        }\n        Bar operator.foo=(Bar, int)\n        {\n            return Bar();\n        }\n    ");
};
tests.anderWithNothingWrong = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        thread int* operator&.foo(thread Foo* foo)\n        {\n            return &foo->x;\n        }\n        int foo()\n        {\n            Foo x;\n            x.x = 13;\n            return x.foo;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 13);
};
tests.anderWithWrongNumberOfArguments = function () {
  checkFail(function () {
    return doPrep("\n            thread int* operator&.foo()\n            {\n                int x;\n                return &x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            thread int* operator&.foo(thread Foo* foo, int blah)\n            {\n                return &foo->x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.anderDoesntReturnPointer = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            int operator&.foo(thread Foo* foo)\n            {\n                return foo->x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.anderDoesntTakeReference = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            thread int* operator&.foo(Foo foo)\n            {\n                return &foo.x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.anderWithArrayRef = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        thread int* operator&.foo(thread Foo[] foo)\n        {\n            return &foo[0].x;\n        }\n        int foo()\n        {\n            Foo x;\n            x.x = 13;\n            return (@x).foo;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 13);
};
tests.pointerIndexGetter = function () {
  checkFail(function () {
    return doPrep("\n            int operator[](device int*, uint)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[](thread int*, uint)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[](threadgroup int*, uint)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[](constant int*, uint)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.loneIndexSetter = function () {
  checkFail(function () {
    return doPrep("\n            int operator[]=(int, uint, int)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.notLoneIndexSetter = function () {
  doPrep("\n        int operator[](int, uint)\n        {\n            return 65;\n        }\n        int operator[]=(int, uint, int)\n        {\n            return 543;\n        }\n    ");
};
tests.indexSetterWithMismatchedType = function () {
  checkFail(function () {
    return doPrep("\n            double operator[](int, uint)\n            {\n                return 5.43;\n            }\n            int operator[]=(int, uint, int)\n            {\n                return 543;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Setter and getter must agree on value type") != -1;
  });
};
tests.indexOperatorWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator[]() { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[](int) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[](int, int, int) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.indexOperatorSetterWrongArgumentLength = function () {
  checkFail(function () {
    return doPrep("\n            int operator[]=() { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[]=(int) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[]=(int, int) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            int operator[]=(int, int, int, int) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.loneIndexSetterPointer = function () {
  checkFail(function () {
    return doPrep("\n            thread int* operator[]=(thread int* ptr, uint, int)\n            {\n                return ptr;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.indexSetterWithNoGetterOverload = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo { }\n            struct Bar { }\n            int operator[](Foo, uint)\n            {\n                return 534;\n            }\n            Bar operator[]=(Bar, uint, int)\n            {\n                return Bar();\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.indexSetterWithNoGetterOverloadFixed = function () {
  doPrep("\n        struct Bar { }\n        int operator[](Bar, uint)\n        {\n            return 534;\n        }\n        Bar operator[]=(Bar, uint, int)\n        {\n            return Bar();\n        }\n    ");
};
tests.indexAnderWithNothingWrong = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        thread int* operator&[](thread Foo* foo, uint)\n        {\n            return &foo->x;\n        }\n        int foo()\n        {\n            Foo x;\n            x.x = 13;\n            return x[666];\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 13);
};
tests.indexAnderWithWrongNumberOfArguments = function () {
  checkFail(function () {
    return doPrep("\n            thread int* operator&[]()\n            {\n                int x;\n                return &x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            thread int* operator&[](thread Foo* foo)\n            {\n                return &foo->x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            thread int* operator&[](thread Foo* foo, uint, uint)\n            {\n                return &foo->x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError;
  });
};
tests.indexAnderDoesntReturnPointer = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            int operator&[](thread Foo* foo, uint)\n            {\n                return foo->x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Return type of ander is not a pointer") != -1;
  });
};
tests.indexAnderDoesntTakeReference = function () {
  checkFail(function () {
    return doPrep("\n            struct Foo {\n                int x;\n            }\n            thread int* operator&[](Foo foo, uint)\n            {\n                return &foo.x;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Parameter to ander is not a reference") != -1;
  });
};
tests.indexAnderWithArrayRef = function () {
  var program = doPrep("\n        struct Foo {\n            int x;\n        }\n        thread int* operator&[](thread Foo[] array, double index)\n        {\n            return &array[uint(index + 1)].x;\n        }\n        int foo()\n        {\n            Foo x;\n            x.x = 13;\n            return (@x)[double(-1)];\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 13);
};
tests.devicePtrPtr = function () {
  checkFail(function () {
    return doPrep("\n            void foo()\n            {\n                device int** p;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Illegal pointer to non-primitive type: int32* device* device") != -1;
  });
};
tests.threadgroupPtrPtr = function () {
  checkFail(function () {
    return doPrep("\n            void foo()\n            {\n                threadgroup int** p;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Illegal pointer to non-primitive type: int32* threadgroup* threadgroup") != -1;
  });
};
tests.constantPtrPtr = function () {
  checkFail(function () {
    return doPrep("\n            void foo()\n            {\n                constant int** p;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Illegal pointer to non-primitive type: int32* constant* constant") != -1;
  });
};
tests.pointerIndexGetterInProtocol = function () {
  var _iterator2 = _createForOfIteratorHelper(addressSpaces),
    _step2;
  try {
    var _loop = function _loop() {
      var addressSpace = _step2.value;
      checkFail(function () {
        return doPrep("\n                protocol Foo {\n                    int operator[](".concat(addressSpace, " Foo*, uint);\n                }\n                struct Bar { }\n                int operator[](Bar, uint) { return 42; }\n            "));
      }, function (e) {
        return e instanceof WTypeError && e.message.indexOf("Cannot have getter for pointer type") != -1;
      });
    };
    for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
      _loop();
    }
  } catch (err) {
    _iterator2.e(err);
  } finally {
    _iterator2.f();
  }
};
tests.loneIndexSetterInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                Foo operator[]=(Foo, uint, int);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Every setter must have a matching getter") != -1;
  });
};
tests.notLoneIndexSetterInProtocol = function () {
  doPrep("\n        protocol Foo {\n            int operator[](Foo, uint);\n            Foo operator[]=(Foo, uint, int);\n        }\n        struct Bar { }\n        int operator[](Bar, uint) { return 42; }\n        Bar operator[]=(Bar, uint, int) { return Bar(); }\n    ");
};
tests.indexSetterWithMismatchedTypeInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                double operator[](Foo, uint);\n                Foo operator[]=(Foo, uint, int);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Setter and getter must agree on value type") != -1;
  });
};
tests.indexOperatorWrongArgumentLengthInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[]();\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Protocol's type variable (Foo) not mentioned in signature") != -1;
  });
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[](Foo);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Incorrect number of parameters") != -1;
  });
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[](Foo, int, int);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Incorrect number of parameters") != -1;
  });
};
tests.indexOperatorSetterWrongArgumentLengthInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[]=();\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Protocol's type variable (Foo) not mentioned in signature") != -1;
  });
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[]=(Foo);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Incorrect number of parameters") != -1;
  });
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[]=(Foo, int);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Incorrect number of parameters") != -1;
  });
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[]=(Foo, int, int, int);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Incorrect number of parameters") != -1;
  });
};
tests.loneIndexSetterPointerInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                thread int* operator[]=(thread Foo* ptr, uint, int);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Cannot have setter for pointer type") != -1;
  });
};
tests.indexSetterWithNoGetterOverloadInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator[](int, Foo);\n                Foo operator[]=(Foo, uint, int);\n            }\n            struct Bar { }\n            int operator[](Bar, uint) { return 42; }\n            Bar operator[]=(Bar, uint, int) { return Bar(); }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Did not find function named operator[]= with arguments Foo,uint32") != -1;
  });
};
tests.indexSetterWithNoGetterOverloadFixedInProtocol = function () {
  doPrep("\n        protocol Foo {\n            int operator[](Foo, uint);\n            Foo operator[]=(Foo, uint, int);\n        }\n        struct Bar { }\n        int operator[](Bar, uint) { return 42; }\n        Bar operator[]=(Bar, uint, int) { return Bar(); }\n    ");
};
tests.indexAnderWithNothingWrongInProtocol = function () {
  var program = doPrep("\n        protocol Foo {\n            thread int* operator&[](thread Foo* foo, uint);\n        }\n        int bar<T:Foo>(T x)\n        {\n            return x[42];\n        }\n        struct Bar { }\n        thread int* operator&[](thread Bar*, uint)\n        {\n            int result = 1234;\n            return &result;\n        }\n        int foo()\n        {\n            return bar(Bar());\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 1234);
};
tests.indexAnderWithWrongNumberOfArgumentsInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                thread int* operator&[]();\n            }\n            struct Bar { }\n            thread int* operator&[](thread Bar*, uint)\n            {\n                int result = 1234;\n                return &result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Protocol's type variable (Foo) not mentioned in signature") != -1;
  });
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                thread int* operator&[](thread Foo* foo);\n            }\n            struct Bar { }\n            thread int* operator&[](thread Bar*, uint)\n            {\n                int result = 1234;\n                return &result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Incorrect number of parameters for operator&[]") != -1;
  });
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                thread int* operator&[](thread Foo* foo, uint, uint);\n            }\n            struct Bar { }\n            thread int* operator&[](thread Bar*, uint)\n            {\n                int result = 1234;\n                return &result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Incorrect number of parameters for operator&[]") != -1;
  });
};
tests.indexAnderDoesntReturnPointerInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                int operator&[](thread Foo* foo, uint);\n            }\n            struct Bar { }\n            thread int* operator&[](thread Bar*, uint)\n            {\n                int result = 1234;\n                return &result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Return type of ander is not a pointer") != -1;
  });
};
tests.indexAnderDoesntTakeReferenceInProtocol = function () {
  checkFail(function () {
    return doPrep("\n            protocol Foo {\n                thread int* operator&[](Foo foo, uint);\n            }\n            struct Bar { }\n            thread int* operator&[](thread Bar*, uint)\n            {\n                int result = 1234;\n                return &result;\n            }\n        ");
  }, function (e) {
    return e instanceof WTypeError && e.message.indexOf("Parameter to ander is not a reference") != -1;
  });
};
tests.indexAnderWithArrayRefInProtocol = function () {
  var program = doPrep("\n        protocol Foo {\n            thread int* operator&[](thread Foo[] array, double index);\n        }\n        int bar<T:Foo>(thread T[] x)\n        {\n            return x[1.5];\n        }\n        struct Bar { }\n        thread int* operator&[](thread Bar[], double)\n        {\n            int result = 1234;\n            return &result;\n        }\n        int foo()\n        {\n            Bar x;\n            return bar(@x);\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 1234);
};
tests.andReturnedArrayRef = function () {
  var program = doPrep("\n        thread int[] getArray()\n        {\n            int[10] x;\n            x[5] = 354;\n            return @x;\n        }\n        int foo()\n        {\n            thread int* ptr = &getArray()[5];\n            return *ptr;\n        }\n    ");
  checkInt(program, callFunction(program, "foo", [], []), 354);
};
okToTest = true;
function doTest() {
  if (!okToTest) throw new Error("Test setup is incomplete.");
  var names = [];
  for (var s in tests) names.push(s);
  names.sort();
  for (var _i3 = 0, _names = names; _i3 < _names.length; _i3++) {
    var _s = _names[_i3];
    tests[_s]();
  }
}
var Benchmark = /*#__PURE__*/function () {
  function Benchmark() {
    _classCallCheck(this, Benchmark);
  }
  return _createClass(Benchmark, [{
    key: "buildStdlib",
    value: function buildStdlib() {
      prepare();
    }
  }, {
    key: "run",
    value: function run() {
      doTest();
    }
  }]);
}();