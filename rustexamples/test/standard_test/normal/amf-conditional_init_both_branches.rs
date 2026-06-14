// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (conditional_init_both_branches test)

fn main() {
    let x: i32;
    if true {
        x = 1;
    } else {
        x = 2;
    }
    let _: i32 = x; // OK, both branches initialize x
}
