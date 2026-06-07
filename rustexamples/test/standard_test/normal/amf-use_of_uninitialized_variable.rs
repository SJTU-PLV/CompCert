// Source: borrowck.rs (use_of_uninitialized_variable test)

fn main() {
    let x: i32;
    let y: i32 = x; //~ ERROR used binding `x` isn't initialized
}
