// Source: borrowck/borrowck-if-with-else.rs

fn main() {
    let x: i32;
    if true {
        let _u1: i32 = 0;
    } else {
        x = 10;
    }
    let _u2: i32 = x; //~ ERROR E0381 use of possibly uninitialized variable
}
