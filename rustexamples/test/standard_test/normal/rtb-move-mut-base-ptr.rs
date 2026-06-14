// Repo: rust-lang/rust
// Source: borrowck/borrowck-move-mut-base-ptr.rs
// Test that attempt to move `&mut` pointer while pointee is borrowed
// yields an error.
//
// Example from compiler/rustc_borrowck/borrowck/README.md



fn foo(t0: &mut i32) {
    let p: &i32 = &*t0; // Freezes `*t0`
    let t1: &mut i32 = t0; //~ ERROR cannot move out of `t0`
    *t1 = 22;
    let _u1: &i32 = p;
}

fn main() {
    let mut x: i32 = 0;
    foo(&mut x);
}
