// Repo: rust-lang/rust
// Source: borrowck/assign-imm-local-twice.rs
// Check that we do not allow assigning twice to an immutable variable. This test also checks a
// few pieces of borrowck diagnostics:
//
// - A multipart borrowck diagnostics that points out the first assignment to an immutable
//   variable, alongside violating assignments that follow subsequently.
// - A suggestion diagnostics to make the immutable binding mutable.

fn main() {
    let v: i32;
    v = 1;
    let _u1: i32 = v;
    v = 2; //~ ERROR cannot assign twice to immutable variable
    let _u2: i32 = v;
}
