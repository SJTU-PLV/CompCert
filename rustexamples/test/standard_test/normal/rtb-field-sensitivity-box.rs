// Repo: rust-lang/rust
// Source: borrowck/borrowck-field-sensitivity.rs
// Field-level sensitivity with Box types: deref/move/borrow conflicts

struct A { a: i32, b: Box<i32> }

fn deref_after_move() {
    let x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    let _u2: i32 = *x.b; //~ ERROR use of moved value: `x.b`
}

fn borrow_after_move() {
    let x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    let p: &Box<i32> = &x.b; //~ ERROR borrow of moved value: `x.b`
    let _u2: i32 = **p;
}

fn move_after_borrow() {
    let x: A = A { a: 1, b: Box::new(2) };
    let p: &Box<i32> = &x.b;
    let _u1: Box<i32> = x.b; //~ ERROR cannot move out of `x.b` because it is borrowed
    let _u2: i32 = **p;
}

fn mut_borrow_after_mut_borrow() {
    let mut x: A = A { a: 1, b: Box::new(2) };
    let p: &mut i32 = &mut x.a;
    let q: &mut i32 = &mut x.a; //~ ERROR cannot borrow `x.a` as mutable more than once
    let _u1: i32 = *p;
    let _u2: i32 = *q;
}

fn move_after_move() {
    let x: A = A { a: 1, b: Box::new(2) };
    let _u1: Box<i32> = x.b;
    let _u2: Box<i32> = x.b; //~ ERROR use of moved value: `x.b`
}

fn copy_after_field_assign_after_uninit() {
    let mut x: A;
    x.a = 1; //~ ERROR E0381
    let _u1: i32 = x.a;
}

fn borrow_after_field_assign_after_uninit() {
    let mut x: A;
    x.a = 1; //~ ERROR E0381
    let p: &i32 = &x.a;
    let _u1: i32 = *p;
}

fn move_after_field_assign_after_uninit() {
    let mut x: A;
    x.b = Box::new(1); //~ ERROR E0381
    let _u1: Box<i32> = x.b;
}

fn main() {
    deref_after_move();
    borrow_after_move();
    move_after_borrow();
    mut_borrow_after_mut_borrow();
    move_after_move();
    copy_after_field_assign_after_uninit();
    borrow_after_field_assign_after_uninit();
    move_after_field_assign_after_uninit();
}
