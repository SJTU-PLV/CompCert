// Source: inputs/smoke-test/polonius-smoke-test.rs (conditional_init function)

fn random() -> bool { true }

fn main() {
    let a: i32;
    if random() { a = 44; }
    let _: i32 = a; //~ ERROR use of possibly uninitialized variable
}
