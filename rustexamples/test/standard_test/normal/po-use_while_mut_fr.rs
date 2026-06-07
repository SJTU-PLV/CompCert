// Source: inputs/smoke-test/polonius-smoke-test.rs (use_while_mut_fr function)

fn use_while_mut_fr(x: &mut i32) -> &mut i32 {
    let y: &mut i32 = &mut *x;
    let z: &mut i32 = x; //~ ERROR cannot use `x` because it was mutably borrowed
    return y;
}

fn main() {
    let mut val: i32 = 42;
    let _: &mut i32 = use_while_mut_fr(&mut val);
}
