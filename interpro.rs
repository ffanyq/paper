fn main() {
    let mut a = 1;
    let mut b = 2;
    let c = 3;
    let d = 4;
    a = b;// (a, b)
    b = c;// (b, c) (a)
    a = d;// (b, c) (a, d)
}