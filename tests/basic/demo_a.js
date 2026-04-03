const a = [1, 2, 3]
{}
{{}}
const key = 1
const a2 = {'a' : 1, '1' : 'a'}
let { a3 = 100 } = a;
const key2 = 'b'
const key3 = 'a' 
a[1]
a['a']
a["1"]
a[key]
let arr=[{n: 5}]; let firstN = arr[0].n;
console.log(a[1], a['a'], a["1"], a[key], a2[key2], a2[key3], a2[1], a3, firstN);
function testBangOptimization(undefinedParam) {
    // 优化3: Bang (!) 运算符优化
    // 触发条件: 操作数类型是 null 或 undefined
    // 优化效果: !x → true (直接替换为 true)
    // 对应代码: InstSimplify.cpp lines 170-174
    // 原理: 如果 undefinedParam 类型推导为 undefined，则 !undefinedParam
    //       会被直接替换为字面量 true

    let result = !undefinedParam;  // undefinedParam 是 undefined，优化为 true
    return result;
}
console.log(testBangOptimization(undefined));