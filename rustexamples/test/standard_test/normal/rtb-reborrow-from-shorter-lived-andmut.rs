// Repo: rust-lang/rust
// Source: borrowck/borrowck-reborrow-from-shorter-lived-andmut.rs
// Test that assignments to an `&mut` pointer which is found in a
// borrowed (but otherwise non-aliasable) location is illegal.

struct S<'a> {
    pointer: &'a mut i32
}

fn copy_borrowed_ptr<'a, 'b>(p: &'a mut S<'b>) -> &'b mut i32 {
    return &mut *p.pointer; //~ ERROR lifetime may not live long enough
}

fn main() {
    let mut x1: i32 = 1;
    {
        let mut y: S = S { pointer: &mut x1 };
        let z: &mut i32 = copy_borrowed_ptr(&mut y);
        *y.pointer = *y.pointer + 1;
        *z = *z + 1;
    }
}
