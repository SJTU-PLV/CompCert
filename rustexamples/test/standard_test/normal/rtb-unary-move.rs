// Repo: rust-lang/rust
// Source: borrowck/borrowck-unary-move.rs
// E0505: cannot move out of Box because it is borrowed

fn foo(x: Box<i32>) -> i32 {
    let y: &i32 = &*x;
    free(x); //~ ERROR cannot move out of `x` because it is borrowed
    return *y;
}

fn free(_x: Box<i32>) {
}

fn main() {
    let _u1: i32 = foo(Box::new(42));
}
