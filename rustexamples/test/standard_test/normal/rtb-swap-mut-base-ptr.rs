// Source: borrowck/borrowck-swap-mut-base-ptr.rs
// Test that attempt to swap `&mut` pointer while pointee is borrowed
// yields an error.
//
// Example from compiler/rustc_borrowck/borrowck/README.md



fn foo<'a>(mut t0: &'a mut i32,
           mut t1: &'a mut i32) {
    let p: &i32 = &*t0;     // Freezes `*t0`
    let tmp: &'a mut i32 = t0;
    t0 = t1;
    t1 = tmp;               //~ ERROR cannot borrow `t0`
    *t1 = 22;
    let _u1: &i32 = p;
}

fn main() {
    let mut x: i32 = 1;
    let mut y: i32 = 2;
    foo(&mut x, &mut y);
}
