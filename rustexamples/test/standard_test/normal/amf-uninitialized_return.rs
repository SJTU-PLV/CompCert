// Source: borrowck.rs (uninitialized_return test)

fn foo() -> i32 {
    let x: i32;
    return x; //~ ERROR use of uninitialized variable `x`
}

fn main() {
    let _: i32 = foo();
}
