// Source: inputs/smoke-test/polonius-smoke-test.rs (use_while_mut function)

fn main() {
    let mut x: i32 = 0;
    let y: &mut i32 = &mut x;
    let z: i32 = x; //~ ERROR cannot use `x` because it was mutably borrowed
    let w: &mut i32 = y;
}
