function f(x) {
    return g(x - 1) + 1;
}

function g(y) {
    if (y === 0) return 1;
    return f(y) * 2;
}

console.log(f(2));