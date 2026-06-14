// Repo: rust-lang/rust
// Source: borrowck/borrowck-uninit.rs
// Simplest case: use of uninitialized variable

fn main() {
    let x: i32;
    let _u1: i32 = x; //~ ERROR E0381 use of possibly uninitialized variable
}
