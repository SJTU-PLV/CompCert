// Source: borrowck/borrowck-while.rs

fn f() -> i32 {
    let mut x: i32;
    while true {
        x = 10;
    }
    return x; //~ ERROR E0381 use of possibly uninitialized variable
}

fn main() {
    let _u1: i32 = f();
}
