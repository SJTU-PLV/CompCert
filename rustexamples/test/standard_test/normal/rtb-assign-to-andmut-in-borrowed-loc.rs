// Repo: rust-lang/rust
// Source: borrowck/borrowck-assign-to-andmut-in-borrowed-loc.rs
// Test that assignments to an `&mut` pointer which is found in a
// borrowed (but otherwise non-aliasable) location is illegal.

struct S<'a> {
    pointer: &'a mut i32
}

fn copy_borrowed_ptr<'a>(p: &'a mut S<'a>) -> &'a mut i32 {
    return &mut *p.pointer;
}

fn main() {
    let mut x1: i32 = 1;
    {
        let mut y: S = S { pointer: &mut x1 };
        let z: &mut i32 = copy_borrowed_ptr(&mut y);
        *y.pointer = *y.pointer + 1; //~ ERROR cannot assign to `*y.pointer` because it is borrowed
        *z = *z + 1;
    }
}
