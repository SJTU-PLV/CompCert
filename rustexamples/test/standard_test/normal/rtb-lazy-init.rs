// Repo: rust-lang/rust
// Source: borrowck/lazy-init.rs
// Both branches initialize the variable — should compile successfully

fn main() {
    let x: i32;
    if true {
        x = 12;
    } else {
        x = 10;
    }
    let _u1: i32 = x; // OK, both branches initialize x
}
