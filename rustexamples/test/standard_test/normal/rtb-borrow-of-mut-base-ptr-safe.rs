// Repo: rust-lang/rust
// Source: borrowck/borrowck-borrow-of-mut-base-ptr-safe.rs
// Test that freezing an `&mut` pointer while referent is
// frozen is legal.
//
// Example from compiler/rustc_borrowck/borrowck/README.md


fn foo<'a>(mut t0: &'a mut i32,
           mut t1: &'a mut i32) {
    let p: &i32 = &*t0; // Freezes `*t0`
    let mut t2: & &mut i32 = &t0;
    let q: &i32 = &**t2; // Freezes `*t0`, but that's ok...
    let r: &i32 = &*t0; // ...after all, could do same thing directly.
    let _u1: &i32 = p;
    let _u2: &i32 = q;
    let _u3: &i32 = r;
    let _u4: &mut i32 = t1;
}

fn main() {
    let mut x: i32 = 1;
    let mut y: i32 = 2;
    foo(&mut x, &mut y);
}
