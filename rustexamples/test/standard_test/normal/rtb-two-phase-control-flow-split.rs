// Repo: rust-lang/rust
// Source: borrowck/two-phase-control-flow-split-before-activation.rs
// Positive test: two-phase borrow across if/else branches

fn maybe() -> bool {
    return false;
}

fn main() {
    let mut a: i32 = 0;
    let mut b: i32 = 0;
    let p: &mut i32;
    if maybe() {
        p = &mut a;
    } else {
        p = &mut b;
    }
    let _u1: &mut i32 = p;
}
