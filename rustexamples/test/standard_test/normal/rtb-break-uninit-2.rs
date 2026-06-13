// Source: borrowck/borrowck-break-uninit-2.rs

fn foo() -> i32 {
    let x: i32;
    while true {
        break;
        x = 0;
    }
    return x; //~ ERROR E0381 use of possibly uninitialized variable
}

fn main() {
    let _u1: i32 = foo();
}
