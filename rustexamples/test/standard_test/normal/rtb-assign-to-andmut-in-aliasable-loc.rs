// Repo: rust-lang/rust
// Source: borrowck/borrowck-assign-to-andmut-in-aliasable-loc.rs
// Test that assignments to an `&mut` pointer which is found in a
// borrowed (but otherwise non-aliasable) location is illegal.

struct S<'a> {
    pointer: &'a mut i32
}

fn a(s: &S) {
    *s.pointer = *s.pointer + 1; //~ ERROR cannot assign
}

fn b(s: &mut S) {
    *s.pointer = *s.pointer + 1;
}

fn c(s: & &mut S) {
    *s.pointer = *s.pointer + 1; //~ ERROR cannot assign
}

fn main() {
    let mut val: i32 = 0;
    let mut s: S = S { pointer: &mut val };
    a(&s);
    b(&mut s);
    c(& &mut s);
}
