class Pair{
    constructor(a, b) {
        this.a = a;
        this.b = b;
    }
}

function addObj(obj) {
    return obj.a + obj.b;
}

function multiply(a, b) {
    return a * b;
}

function substractObj(obj) {
    return obj.a - obj.b;
}

function callMultiply(callback) {
   return callback(4, 8);
}

function wrap() {
    function minus(obj) {
        return obj.a - obj.b;
    }
    return minus({ a: 10, b: 3 });
}

let i = addObj(new Pair(1, 5));
let j = substractObj({ a: i, b: i + i });
let k = callMultiply(multiply);
let l = wrap();
console.log(i, j, k, l);


