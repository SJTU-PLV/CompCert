// Source: borrowck/borrowck-init-op-equal.rs

fn test() {
    let v: i32;
    v = v + 1; //~ ERROR E0381
    let _u1: i32 = v;
}

fn main() {
    test();
}
