// 死锁检测，包括函数自引用，类自引用等

// test1
function f(x, unused) {
    if (x === 0) return 0;
    return f(x - 1, unused);
}

// test2
class A{
    x = 1;
    get_x(x) {
        return x.x;
    }
}
const ret = new A().get_x(new A());

// test3
let namespaces;
namespaces = typeof namespaces === 'string' ? [namespaces] : namespaces || ['translation'];

// test4
let a = { data: 1};
let b = { ref: a, data : 'b'};
a.ref = b;


// test5
class B{
    x;
    y = 1;
    constructor(x) {
        this.x = x;
    }
}
const b1 = new B(2);
const b2 = new B(b1);

console.log(f(5, f), ret, namespaces, a.ref.data, b.ref.data, b1, b2);