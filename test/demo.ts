let x = new Command();
let y = x;

interface Point {
    x: number;
    y: number;
}

let p: Point = getPoint();
let q: Point = p;
  
  
function add(a: number, b: number): number {
    return a + b;
}

let result = add(1, 2);

class Person {
    name: string;
    constructor(name: string) {
      this.name = name;
    }
}
  
let alice = new Person("Alice");
  