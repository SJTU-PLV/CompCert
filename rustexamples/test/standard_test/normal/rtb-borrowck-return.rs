// Repo: rust-lang/rust
// Source: borrowck/borrowck-return.rs

fn f() -> i32 {
    let x: i32;
    return x; //~ ERROR E0381 use of possibly uninitialized variable
}

fn main() {
    f();
}
