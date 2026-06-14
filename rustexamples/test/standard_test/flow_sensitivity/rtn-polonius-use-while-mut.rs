// Source: nll/polonius/polonius-smoke-test.rs
// Polonius: mutably borrowed variable used while borrow is live

fn use_while_mut() {
    let mut x: i32 = 0;
    let y: &mut i32 = &mut x;
    let z: i32 = x; //~ ERROR E0503 cannot use `x` because it was mutably borrowed
    let _u1: &mut i32 = y;
}

fn main() {
    use_while_mut();
}
