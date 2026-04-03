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

// NOTE: The next line is line 28, and we rely on this in Prepare.js.
var standardLibrary = "\n// This is the WSL standard library. Implementations of all of these things are in\n// Intrinsics.js.\n\n// Need to bootstrap void first.\nnative typedef void;\n\nnative typedef uint8;\nnative typedef int32;\nnative typedef uint32;\nnative typedef bool;\ntypedef int = int32;\ntypedef uint = uint32;\n\nnative typedef float32;\nnative typedef float64;\ntypedef float = float32;\ntypedef double = float64;\n\nnative operator int32(uint32);\nnative operator int32(uint8);\nnative operator int32(float);\nnative operator int32(double);\nnative operator uint32(int32);\nnative operator uint32(uint8);\nnative operator uint32(float);\nnative operator uint32(double);\nnative operator uint8(int32);\nnative operator uint8(uint32);\nnative operator uint8(float);\nnative operator uint8(double);\nnative operator float(int32);\nnative operator float(uint32);\nnative operator float(uint8);\nnative operator float(double);\nnative operator double(float);\nnative operator double(int32);\nnative operator double(uint32);\nnative operator double(uint8);\n\nnative int operator+(int, int);\nnative uint operator+(uint, uint);\nuint8 operator+(uint8 a, uint8 b) { return uint8(uint(a) + uint(b)); }\nnative float operator+(float, float);\nnative double operator+(double, double);\nint operator++(int value) { return value + 1; }\nuint operator++(uint value) { return value + 1; }\nuint8 operator++(uint8 value) { return value + 1; }\nnative int operator-(int, int);\nnative uint operator-(uint, uint);\nuint8 operator-(uint8 a, uint8 b) { return uint8(uint(a) - uint(b)); }\nnative float operator-(float, float);\nnative double operator-(double, double);\nint operator--(int value) { return value - 1; }\nuint operator--(uint value) { return value - 1; }\nuint8 operator--(uint8 value) { return value - 1; }\nnative int operator*(int, int);\nnative uint operator*(uint, uint);\nuint8 operator*(uint8 a, uint8 b) { return uint8(uint(a) * uint(b)); }\nnative float operator*(float, float);\nnative double operator*(double, double);\nnative int operator/(int, int);\nnative uint operator/(uint, uint);\nuint8 operator/(uint8 a, uint8 b) { return uint8(uint(a) / uint(b)); }\nnative int operator&(int, int);\nnative int operator|(int, int);\nnative int operator^(int, int);\nnative int operator~(int);\nnative int operator<<(int, uint);\nnative int operator>>(int, uint);\nnative uint operator&(uint, uint);\nnative uint operator|(uint, uint);\nnative uint operator^(uint, uint);\nnative uint operator~(uint);\nnative uint operator<<(uint, uint);\nnative uint operator>>(uint, uint);\nuint8 operator&(uint8 a, uint8 b) { return uint8(uint(a) & uint(b)); }\nuint8 operator|(uint8 a, uint8 b) { return uint8(uint(a) | uint(b)); }\nuint8 operator^(uint8 a, uint8 b) { return uint8(uint(a) ^ uint(b)); }\nuint8 operator~(uint8 value) { return uint8(~uint(value)); }\nuint8 operator<<(uint8 a, uint b) { return uint8(uint(a) << (b & 7)); }\nuint8 operator>>(uint8 a, uint b) { return uint8(uint(a) >> (b & 7)); }\nnative float operator/(float, float);\nnative double operator/(double, double);\nnative bool operator==(int, int);\nnative bool operator==(uint, uint);\nbool operator==(uint8 a, uint8 b) { return uint(a) == uint(b); }\nnative bool operator==(bool, bool);\nnative bool operator==(float, float);\nnative bool operator==(double, double);\nnative bool operator<(int, int);\nnative bool operator<(uint, uint);\nbool operator<(uint8 a, uint8 b) { return uint(a) < uint(b); }\nnative bool operator<(float, float);\nnative bool operator<(double, double);\nnative bool operator<=(int, int);\nnative bool operator<=(uint, uint);\nbool operator<=(uint8 a, uint8 b) { return uint(a) <= uint(b); }\nnative bool operator<=(float, float);\nnative bool operator<=(double, double);\nnative bool operator>(int, int);\nnative bool operator>(uint, uint);\nbool operator>(uint8 a, uint8 b) { return uint(a) > uint(b); }\nnative bool operator>(float, float);\nnative bool operator>(double, double);\nnative bool operator>=(int, int);\nnative bool operator>=(uint, uint);\nbool operator>=(uint8 a, uint8 b) { return uint(a) >= uint(b); }\nnative bool operator>=(float, float);\nnative bool operator>=(double, double);\n\nbool operator&(bool a, bool b)\n{\n    if (a)\n        return b;\n    return false;\n}\n\nbool operator|(bool a, bool b)\n{\n    if (a)\n        return true;\n    if (b)\n        return true;\n    return false;\n}\n\nbool operator^(bool a, bool b)\n{\n    if (a)\n        return !b;\n    return b;\n}\n\nbool operator~(bool value)\n{\n    return !value;\n}\n\nprotocol Addable {\n    Addable operator+(Addable, Addable);\n}\n\nprotocol Equatable {\n    bool operator==(Equatable, Equatable);\n}\n\nrestricted operator<T> T()\n{\n    T defaultValue;\n    return defaultValue;\n}\n\nrestricted operator<T> T(T x)\n{\n    return x;\n}\n\noperator<T:Equatable> bool(T x)\n{\n    return x != T();\n}\n\nstruct vec2<T> {\n    T x;\n    T y;\n}\n\ntypedef int2 = vec2<int>;\ntypedef uint2 = vec2<uint>;\ntypedef float2 = vec2<float>;\ntypedef double2 = vec2<double>;\n\noperator<T> vec2<T>(T x, T y)\n{\n    vec2<T> result;\n    result.x = x;\n    result.y = y;\n    return result;\n}\n\nbool operator==<T:Equatable>(vec2<T> a, vec2<T> b)\n{\n    return a.x == b.x && a.y == b.y;\n}\n\nthread T* operator&[]<T>(thread vec2<T>* foo, uint index)\n{\n    if (index == 0)\n        return &foo->x;\n    if (index == 1)\n        return &foo->y;\n    trap;\n}\n\nstruct vec3<T> {\n    T x;\n    T y;\n    T z;\n}\n\ntypedef int3 = vec3<int>;\ntypedef uint3 = vec3<uint>;\ntypedef float3 = vec3<float>;\ntypedef double3 = vec3<double>;\n\noperator<T> vec3<T>(T x, T y, T z)\n{\n    vec3<T> result;\n    result.x = x;\n    result.y = y;\n    result.z = z;\n    return result;\n}\n\noperator<T> vec3<T>(vec2<T> v2, T z)\n{\n    vec3<T> result;\n    result.x = v2.x;\n    result.y = v2.y;\n    result.z = z;\n    return result;\n}\n\noperator<T> vec3<T>(T x, vec2<T> v2)\n{\n    vec3<T> result;\n    result.x = x;\n    result.y = v2.x;\n    result.z = v2.y;\n    return result;\n}\n\nbool operator==<T:Equatable>(vec3<T> a, vec3<T> b)\n{\n    return a.x == b.x && a.y == b.y && a.z == b.z;\n}\n\nthread T* operator&[]<T>(thread vec3<T>* foo, uint index)\n{\n    if (index == 0)\n        return &foo->x;\n    if (index == 1)\n        return &foo->y;\n    if (index == 2)\n        return &foo->z;\n    trap;\n}\n\nstruct vec4<T> {\n    T x;\n    T y;\n    T z;\n    T w;\n}\n\ntypedef int4 = vec4<int>;\ntypedef uint4 = vec4<uint>;\ntypedef float4 = vec4<float>;\ntypedef double4 = vec4<double>;\n\noperator<T> vec4<T>(T x, T y, T z, T w)\n{\n    vec4<T> result;\n    result.x = x;\n    result.y = y;\n    result.z = z;\n    result.w = w;\n    return result;\n}\n\noperator<T> vec4<T>(vec2<T> v2, T z, T w)\n{\n    vec4<T> result;\n    result.x = v2.x;\n    result.y = v2.y;\n    result.z = z;\n    result.w = w;\n    return result;\n}\n\noperator<T> vec4<T>(T x, vec2<T> v2, T w)\n{\n    vec4<T> result;\n    result.x = x;\n    result.y = v2.x;\n    result.z = v2.y;\n    result.w = w;\n    return result;\n}\n\noperator<T> vec4<T>(T x, T y, vec2<T> v2)\n{\n    vec4<T> result;\n    result.x = x;\n    result.y = y;\n    result.z = v2.x;\n    result.w = v2.y;\n    return result;\n}\n\noperator<T> vec4<T>(vec2<T> v2a, vec2<T> v2b)\n{\n    vec4<T> result;\n    result.x = v2a.x;\n    result.y = v2a.y;\n    result.z = v2b.x;\n    result.w = v2b.y;\n    return result;\n}\n\noperator<T> vec4<T>(vec3<T> v3, T w)\n{\n    vec4<T> result;\n    result.x = v3.x;\n    result.y = v3.y;\n    result.z = v3.z;\n    result.w = w;\n    return result;\n}\n\noperator<T> vec4<T>(T x, vec3<T> v3)\n{\n    vec4<T> result;\n    result.x = x;\n    result.y = v3.x;\n    result.z = v3.y;\n    result.w = v3.z;\n    return result;\n}\n\nbool operator==<T:Equatable>(vec4<T> a, vec4<T> b)\n{\n    return a.x == b.x && a.y == b.y && a.z == b.z && a.w == b.w;\n}\n\nthread T* operator&[]<T>(thread vec4<T>* foo, uint index)\n{\n    if (index == 0)\n        return &foo->x;\n    if (index == 1)\n        return &foo->y;\n    if (index == 2)\n        return &foo->z;\n    if (index == 3)\n        return &foo->w;\n    trap;\n}\n\nnative thread T* operator&[]<T>(thread T[], uint);\nnative threadgroup T* operator&[]<T>(threadgroup T[], uint);\nnative device T* operator&[]<T>(device T[], uint);\nnative constant T* operator&[]<T>(constant T[], uint);\n\nnative uint operator.length<T>(thread T[]);\nnative uint operator.length<T>(threadgroup T[]);\nnative uint operator.length<T>(device T[]);\nnative uint operator.length<T>(constant T[]);\n\nuint operator.length<T, uint length>(T[length])\n{\n    return length;\n}\n";
function intToString(x) {
  switch (x) {
    case 0:
      return "x";
    case 1:
      return "y";
    case 2:
      return "z";
    case 3:
      return "w";
    default:
      throw new Error("Could not generate standard library.");
  }
}

// There are 481 swizzle operators. Let's not list them explicitly.
function _generateSwizzle(maxDepth, maxItems, array) {
  if (!array) array = [];
  if (array.length == maxDepth) {
    var _result = "vec".concat(array.length, "<T> operator.").concat(array.join(""), "<T>(vec").concat(maxItems, "<T> v)\n{\n    vec").concat(array.length, "<T> result;\n");
    for (var i = 0; i < array.length; ++i) {
      _result += "    result.".concat(intToString(i), " = v.").concat(array[i], ";\n");
    }
    _result += "    return result;\n}\n";
    return _result;
  }
  var result = "";
  for (var _i = 0; _i < maxItems; ++_i) {
    array.push(intToString(_i));
    result += _generateSwizzle(maxDepth, maxItems, array);
    array.pop();
  }
  return result;
}
for (var maxDepth = 2; maxDepth <= 4; maxDepth++) {
  for (var maxItems = 2; maxItems <= 4; maxItems++) standardLibrary += _generateSwizzle(maxDepth, maxItems);
}