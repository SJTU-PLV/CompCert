// Repo: rust-lang/rust
// Source: borrowck/borrowck-issue-14498.rs
// Box<&mut T> borrow interactions: immutable Box prevents mutation,
// mutable Box allows mutation but borrow blocks it

struct A { a: i32 }
struct B<'a> { a: Box<&'a mut i32> }

fn indirect_write_to_imm_box() {
    let mut x: i32 = 1;
    let y: Box<&mut i32> = Box::new(&mut x);
    let p: &Box<&mut i32> = &y;
    ***p = 2; //~ ERROR cannot assign to `***p` (immutable ref to Box)
    let _u1: &Box<&mut i32> = p;
}

fn borrow_in_var_from_var() {
    let mut x: i32 = 1;
    let mut y: Box<&mut i32> = Box::new(&mut x);
    let p: &Box<&mut i32> = &y;
    let q: &i32 = &***p;
    **y = 2; //~ ERROR cannot assign to `**y` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn borrow_in_var_from_var_via_imm_box() {
    let mut x: i32 = 1;
    let y: Box<&mut i32> = Box::new(&mut x);
    let p: &Box<&mut i32> = &y;
    let q: &i32 = &***p;
    **y = 2; //~ ERROR cannot assign to `**y` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn borrow_in_var_from_field() {
    let mut x: A = A { a: 1 };
    let mut y: Box<&mut i32> = Box::new(&mut x.a);
    let p: &Box<&mut i32> = &y;
    let q: &i32 = &***p;
    **y = 2; //~ ERROR cannot assign to `**y` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn borrow_in_var_from_field_via_imm_box() {
    let mut x: A = A { a: 1 };
    let y: Box<&mut i32> = Box::new(&mut x.a);
    let p: &Box<&mut i32> = &y;
    let q: &i32 = &***p;
    **y = 2; //~ ERROR cannot assign to `**y` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn borrow_in_field_from_var() {
    let mut x: i32 = 1;
    let mut y: B = B { a: Box::new(&mut x) };
    let p: &Box<&mut i32> = &y.a;
    let q: &i32 = &***p;
    **y.a = 2; //~ ERROR cannot assign to `**y.a` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn borrow_in_field_from_var_via_imm_box() {
    let mut x: i32 = 1;
    let y: B = B { a: Box::new(&mut x) };
    let p: &Box<&mut i32> = &y.a;
    let q: &i32 = &***p;
    **y.a = 2; //~ ERROR cannot assign to `**y.a` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn borrow_in_field_from_field() {
    let mut x: A = A { a: 1 };
    let mut y: B = B { a: Box::new(&mut x.a) };
    let p: &Box<&mut i32> = &y.a;
    let q: &i32 = &***p;
    **y.a = 2; //~ ERROR cannot assign to `**y.a` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn borrow_in_field_from_field_via_imm_box() {
    let mut x: A = A { a: 1 };
    let y: B = B { a: Box::new(&mut x.a) };
    let p: &Box<&mut i32> = &y.a;
    let q: &i32 = &***p;
    **y.a = 2; //~ ERROR cannot assign to `**y.a` because it is borrowed
    let _u1: &Box<&mut i32> = p;
    let _u2: &i32 = q;
}

fn main() {
    indirect_write_to_imm_box();
    borrow_in_var_from_var();
    borrow_in_var_from_var_via_imm_box();
    borrow_in_var_from_field();
    borrow_in_var_from_field_via_imm_box();
    borrow_in_field_from_var();
    borrow_in_field_from_var_via_imm_box();
    borrow_in_field_from_field();
    borrow_in_field_from_field_via_imm_box();
}
