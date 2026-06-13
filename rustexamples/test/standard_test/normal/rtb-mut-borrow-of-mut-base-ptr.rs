// Source: borrowck/borrowck-mut-borrow-of-mut-base-ptr.rs
// Test that attempt to mutably borrow `&mut` pointer while pointee is
// borrowed yields an error.
//
// Example from compiler/rustc_borrowck/borrowck/README.md



fn foo<'a>(mut t0: &'a mut i32,
           mut t1: &'a mut i32) {
    let p: &i32 = &*t0;     // Freezes `*t0`
    let mut t2: &mut &mut i32 = &mut t0; //~ ERROR cannot borrow `t0`
    **t2 = **t2 + 1;        // Mutates `*t0`
    let _u1: &i32 = p;
    let _u2: &mut i32 = t1;
}

fn bar<'a>(mut t0: &'a mut i32,
           mut t1: &'a mut i32) {
    let p: &mut i32 = &mut *t0; // Claims `*t0`
    let mut t2: &mut &mut i32 = &mut t0; //~ ERROR cannot borrow `t0`
    **t2 = **t2 + 1;              // Mutates `*t0` but not through `*p`
    let _u1: &mut i32 = p;
    let _u2: &mut i32 = t1;
}

fn main() {
    let mut x: i32 = 1;
    let mut y: i32 = 2;
    foo(&mut x, &mut y);
    bar(&mut x, &mut y);
}
