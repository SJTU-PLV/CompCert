// Source: inputs/smoke-test/polonius-smoke-test.rs (return_ref_to_local function)

fn return_ref_to_local<'a>() -> &'a i32 {
    let x: i32 = 0;
    return &x; //~ ERROR cannot return reference to local variable
}

fn main() {
    let _: &i32 = return_ref_to_local();
}
