// Repo: rust-lang/rust
// Source: borrowck/immut-function-arguments.rs
// E0594: cannot assign to `*y` because argument is immutable

fn f(y: Box<i32>) {
    *y = 5; //~ ERROR cannot assign
}

fn main() {
    f(Box::new(0));
}
