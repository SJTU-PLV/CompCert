// Source: borrowck/borrowck-for-loop-uninitialized-binding.rs
// for loop body may not execute — variable may be uninitialized (adapted to while)

fn f() -> i32 {
    let mut x: i32;
    let mut i: i32 = 0;
    while i < 0 {
        x = 10;
        i = i + 1;
    }
    return x; //~ ERROR E0381
}

fn main() {
    let _u1: i32 = f();
}
