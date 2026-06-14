// Repo: rust-lang/polonius
// Source: inputs/smoke-test/polonius-smoke-test.rs (position_dependent_outlives function)

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
    let _: i32 = val;
}
