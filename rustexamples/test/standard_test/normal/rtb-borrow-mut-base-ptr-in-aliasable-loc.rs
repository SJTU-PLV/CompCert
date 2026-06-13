// Source: borrowck/borrowck-borrow-mut-base-ptr-in-aliasable-loc.rs
// Test that attempt to reborrow an `&mut` pointer in an aliasable
// location yields an error.
//
// Example from compiler/rustc_borrowck/borrowck/README.md

fn foo(t0: & &mut i32) {
    let t1: & &mut i32 = t0;
    let p: &i32 = &**t0;
    **t1 = 22; //~ ERROR cannot assign
    let _u1: &i32 = p;
}

fn foo3(t0: &mut &mut i32) {
    let t1: &mut &mut i32 = &mut *t0;
    let p: &i32 = &**t0; //~ ERROR cannot borrow
    **t1 = 22;
    let _u1: &i32 = p;
}

fn foo4(t0: & &mut i32) {
    let x: &mut i32 = &mut **t0; //~ ERROR cannot borrow
    let _u1: &mut i32 = x;
}

fn main() {
    let mut val: i32 = 42;
    let mut r: &mut i32 = &mut val;
    foo(& &mut r);
    foo3(&mut r);
    foo4(& &mut r);
}
