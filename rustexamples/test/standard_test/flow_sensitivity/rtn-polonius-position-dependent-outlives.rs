// Repo: rust-lang/rust
// Source: nll/polonius/polonius-smoke-test.rs
// Quintessential Polonius test: NLL fails, Polonius passes

fn position_dependent_outlives(x: &mut i32) -> &mut i32 {
    let y: &mut i32 = &mut *x;
    if true {
        return y;
    } else {
        *x = 0;
        return x;
    }
}

fn main() {
    let mut val: i32 = 42;
    let result: &mut i32 = position_dependent_outlives(&mut val);
    *result = *result + 1;
    let _u1: i32 = val;
}
