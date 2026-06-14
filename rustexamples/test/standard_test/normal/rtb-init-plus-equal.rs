// Repo: rust-lang/rust
// Source: borrowck/borrowck-init-plus-equal.rs
// E0381: using uninitialized variable in binary operation

fn test() {
    let mut v: i32;
    v = v + 1; //~ ERROR E0381
    let _u1: i32 = v;
}

fn main() {
    test();
}
