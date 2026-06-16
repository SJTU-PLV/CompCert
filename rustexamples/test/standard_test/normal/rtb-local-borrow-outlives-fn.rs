// Repo: rust-lang/rust
// Source: borrowck/borrowck-local-borrow-outlives-fn.rs

fn cplusplus_mode<'a>(x: i32) -> &'a i32 {
    return &x; //~ ERROR cannot return reference to function parameter `x` [E0515]
}

fn main() {
    let _u1: &i32 = cplusplus_mode(0);
}
