// Repo: rust-lang/rust
// Source: borrowck/borrowck-while-break.rs

fn test(cond: bool) -> i32 {
    let v: i32;
    while (cond) {
        v = 3;
        break;
    }
    return v; //~ ERROR E0381 use of possibly uninitialized variable
}

fn main() {
    let _u1: i32 = test(true);
}
