// Repo: rust-lang/rust
// Source: borrowck/issue-46471.rs

fn foo() -> &'static i32 {
    let x: i32 = 0;
    return &x; //~ ERROR E0515 cannot return reference to local variable
}

fn main() {
    let _u1: &i32 = foo();
}
