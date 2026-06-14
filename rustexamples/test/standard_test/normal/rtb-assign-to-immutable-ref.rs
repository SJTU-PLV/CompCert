// Repo: rust-lang/rust
// Source: borrowck/assignment-to-immutable-ref.rs
// Regression test for issue <https://github.com/rust-lang/rust/issues/51515>
// Test that assigning through an immutable reference (`&`) correctly yields
// an assignment error (E0594) and suggests using a mutable reference.

fn main() {
    let x: i32 = 16;
    let foo: &i32 = &x;
    *foo = 32; //~ ERROR cannot assign to `*foo`, which is behind a `&` reference
    let bar: &i32 = foo;
    *bar = 64; //~ ERROR cannot assign to `*bar`, which is behind a `&` reference
    let _u1: &i32 = bar;
}
