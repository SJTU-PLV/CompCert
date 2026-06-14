// Repo: rust-lang/rust
// Source: nll/polonius/polonius-smoke-test.rs

fn foo<'a, 'b>(p: &'b &'a mut i32) -> &'b i32 {
    return &**p;
}

fn main() {
    let mut val: i32 = 1;
    let s: &mut i32 = &mut val;
    let r: &mut i32 = &mut *s;
    let tmp: &i32 = foo(&r);
    let _u1: i32 = *s; //~ ERROR cannot use `*s` because it was mutably borrowed
    let _u2: i32 = *tmp;
}
