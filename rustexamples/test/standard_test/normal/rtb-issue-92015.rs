// Repo: rust-lang/rust
// Source: borrowck/issue-92015.rs
// E0594: cannot assign through & reference (immutable reference mutation)

fn main() {
    let x: i32 = 0;
    let foo: &i32 = &x;
    *foo = 1; //~ ERROR E0594
}
