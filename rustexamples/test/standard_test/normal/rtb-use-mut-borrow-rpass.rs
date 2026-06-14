// Repo: rust-lang/rust
// Source: borrowck/borrowck-use-mut-borrow-rpass.rs
// Positive test: borrowing one field of struct with Box does not block
// using other fields (field-level sensitivity)

struct A { a: i32, b: Box<i32> }

fn field_copy_after_field_borrow() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let p: &mut Box<i32> = &mut x.b;
    let _u1: i32 = x.a;
    **p = 3;
}

fn field_deref_after_field_borrow() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let p: &mut i32 = &mut x.a;
    let _u1: i32 = *x.b;
    *p = 3;
}

fn field_move_after_field_borrow() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let p: &mut i32 = &mut x.a;
    let _u1: Box<i32> = x.b;
    *p = 3;
}

fn main() {
    field_copy_after_field_borrow();
    field_deref_after_field_borrow();
    field_move_after_field_borrow();
}
