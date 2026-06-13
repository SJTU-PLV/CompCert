// Source: borrowck/borrowck-local-borrow-outlives-fn.rs

fn cplusplus_mode(x: i32) -> &'static i32 {
    return &x; //~ ERROR cannot return reference to function parameter `x` [E0515]
}

fn main() {
    let _u1: &i32 = cplusplus_mode(0);
}
