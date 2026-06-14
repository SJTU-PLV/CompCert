// Source: nll/polonius/polonius-smoke-test.rs

fn return_ref_to_local() -> &'static i32 {
    let x: i32 = 0;
    return &x; //~ ERROR E0515 cannot return reference to local variable
}

fn main() {
    let _u1: &i32 = return_ref_to_local();
}
