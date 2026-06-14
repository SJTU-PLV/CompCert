// Repo: rust-lang/rust
// Source: borrowck/borrowck-field-sensitivity-rpass.rs
// Positive tests: field-level sensitivity with Box — borrowing/moving one field
// does not block using other fields

struct A { a: i32, b: Box<i32> }
struct B { a: Box<i32>, b: Box<i32> }

fn move_after_copy() {
    let x: A = A { a: 1, b: Box::new(2) };
    let _u1: i32 = x.a;
    let _u2: Box<i32> = x.b;
}

fn copy_after_move() {
    let x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    let _u2: i32 = x.a;
}

fn borrow_after_move() {
    let x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    let p: &i32 = &x.a;
    let _u2: i32 = *p;
}

fn move_after_borrow() {
    let x: A = A { a: 1, b: Box::new(2) };
    let p: &i32 = &x.a;
    let _u1: Box<i32> = x.b;
    let _u2: i32 = *p;
}

fn mut_borrow_after_mut_borrow() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let p: &mut i32 = &mut x.a;
    let q: &mut Box<i32> = &mut x.b;
    let _u1: i32 = *p;
    let _u2: i32 = **q;
}

fn move_after_move() {
    let x: B = B { a: Box::new(1), b: Box::new(2) };
    let _u1: Box<i32> = x.a;
    let _u2: Box<i32> = x.b;
}

fn copy_after_assign_after_move() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    x = A { a: 3, b: Box::new(4) };
    let _u2: i32 = *x.b;
}

fn copy_after_field_assign_after_move() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    x.b = Box::new(3);
    let _u2: i32 = *x.b;
}

fn borrow_after_assign_after_move() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    x = A { a: 3, b: Box::new(4) };
    let p: &Box<i32> = &x.b;
    let _u2: i32 = **p;
}

fn borrow_after_field_assign_after_move() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    x.b = Box::new(3);
    let p: &Box<i32> = &x.b;
    let _u2: i32 = **p;
}

fn move_after_assign_after_move() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    x = A { a: 3, b: Box::new(4) };
    let _u2: Box<i32> = x.b;
}

fn move_after_field_assign_after_move() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    x.b = Box::new(3);
    let _u2: Box<i32> = x.b;
}

fn copy_after_assign_after_uninit() {
    let mut x: A;
    x = A { a: 1, b: Box::new(2) };
    let _u1: i32 = x.a;
}

fn borrow_after_assign_after_uninit() {
    let mut x: A;
    x = A { a: 1, b: Box::new(2) };
    let p: &i32 = &x.a;
    let _u1: i32 = *p;
}

fn move_after_assign_after_uninit() {
    let mut x: A;
    x = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
}

fn main() {
    move_after_copy();
    copy_after_move();
    borrow_after_move();
    move_after_borrow();
    mut_borrow_after_mut_borrow();
    move_after_move();
    copy_after_assign_after_move();
    copy_after_field_assign_after_move();
    borrow_after_assign_after_move();
    borrow_after_field_assign_after_move();
    move_after_assign_after_move();
    move_after_field_assign_after_move();
    copy_after_assign_after_uninit();
    borrow_after_assign_after_uninit();
    move_after_assign_after_uninit();
}
