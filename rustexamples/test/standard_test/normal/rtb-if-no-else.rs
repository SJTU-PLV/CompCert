// Repo: rust-lang/rust
// Source: borrowck/borrowck-if-no-else.rs

fn main() {
    let x: i32;
    if true {
        x = 10;
    }
    let _u1: i32 = x; //~ ERROR E0381 use of possibly uninitialized variable
}
