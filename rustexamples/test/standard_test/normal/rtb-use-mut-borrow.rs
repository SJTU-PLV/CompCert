// Source: borrowck/borrowck-use-mut-borrow.rs
// Mut borrow conflicts: use of variable/field while mutably borrowed (with Box)

struct A { a: i32, b: i32 }
struct B { a: i32, b: Box<i32> }

fn var_copy_after_var_borrow() {
    let mut x: i32 = 1;
    let p: &mut i32 = &mut x;
    let _u1: i32 = x; //~ ERROR cannot use `x` because it was mutably borrowed
    *p = 2;
}

fn var_copy_after_field_borrow() {
    let mut x: A = A { a: 1, b: 2 };
    let p: &mut i32 = &mut x.a;
    let _u1: A = x; //~ ERROR cannot use `x` because it was mutably borrowed
    *p = 3;
}

fn field_copy_after_var_borrow() {
    let mut x: A = A { a: 1, b: 2 };
    let p: &mut A = &mut x;
    let _u1: i32 = x.a; //~ ERROR cannot use `x.a` because it was mutably borrowed
    p.a = 3;
}

fn field_copy_after_field_borrow() {
    let mut x: A = A { a: 1, b: 2 };
    let p: &mut i32 = &mut x.a;
    let _u1: i32 = x.a; //~ ERROR cannot use `x.a` because it was mutably borrowed
    *p = 3;
}

fn var_deref_after_var_borrow() {
    let mut x: Box<i32> = Box::new(1);
    let p: &mut Box<i32> = &mut x;
    let _u1: i32 = *x; //~ ERROR cannot use `*x` because it was mutably borrowed
    **p = 2;
}

fn field_deref_after_var_borrow() {
    let mut x: B = B { a: 1, b: Box::new(2) };
    let p: &mut B = &mut x;
    let _u1: i32 = *x.b; //~ ERROR cannot use `*x.b` because it was mutably borrowed
    p.a = 3;
}

fn field_deref_after_field_borrow() {
    let mut x: B = B { a: 1, b: Box::new(2) };
    let p: &mut Box<i32> = &mut x.b;
    let _u1: i32 = *x.b; //~ ERROR cannot use `*x.b` because it was mutably borrowed
    **p = 3;
}

fn main() {
    var_copy_after_var_borrow();
    var_copy_after_field_borrow();
    field_copy_after_var_borrow();
    field_copy_after_field_borrow();
    var_deref_after_var_borrow();
    field_deref_after_var_borrow();
    field_deref_after_field_borrow();
}
