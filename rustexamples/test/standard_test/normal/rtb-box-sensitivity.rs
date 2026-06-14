// Repo: rust-lang/rust
// Source: borrowck/borrowck-box-sensitivity.rs
// Test that `Box<T>` is treated specially by borrow checking.

struct A {
    x: Box<i32>,
    y: i32
}

struct B {
    x: Box<i32>,
    y: Box<i32>
}

struct C {
    x: Box<A>,
    y: i32
}

struct D {
    x: Box<A>,
    y: Box<i32>
}

fn copy_after_move() {
    let a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let _x: Box<i32> = (*a).x;
    let _y: i32 = (*a).y;
}

fn move_after_move() {
    let a: Box<B> = Box::new(B { x: Box::new(0), y: Box::new(1) });
    let _x: Box<i32> = (*a).x;
    let _y: Box<i32> = (*a).y;
}

fn borrow_after_move() {
    let a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let _x: Box<i32> = (*a).x;
    let _y: &i32 = &(*a).y;
}

fn move_after_borrow() {
    let a: Box<B> = Box::new(B { x: Box::new(0), y: Box::new(1) });
    let _x: &Box<i32> = &(*a).x;
    let _y: Box<i32> = (*a).y;
    let _u1: &Box<i32> = _x;
}

fn copy_after_mut_borrow() {
    let mut a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let _x: &mut Box<i32> = &mut (*a).x;
    let _y: i32 = (*a).y;
    let _u1: &mut Box<i32> = _x;
}

fn move_after_mut_borrow() {
    let mut a: Box<B> = Box::new(B { x: Box::new(0), y: Box::new(1) });
    let _x: &mut Box<i32> = &mut (*a).x;
    let _y: Box<i32> = (*a).y;
    let _u1: &mut Box<i32> = _x;
}

fn borrow_after_mut_borrow() {
    let mut a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let _x: &mut Box<i32> = &mut (*a).x;
    let _y: &i32 = &(*a).y;
    let _u1: &mut Box<i32> = _x;
}

fn mut_borrow_after_borrow() {
    let mut a: Box<A> = Box::new(A { x: Box::new(0), y: 1 });
    let _x: &Box<i32> = &(*a).x;
    let _y: &mut i32 = &mut (*a).y;
    let _u1: &Box<i32> = _x;
}

fn copy_after_move_nested() {
    let a: Box<C> = Box::new(C { x: Box::new(A { x: Box::new(0), y: 1 }), y: 2 });
    let _x: Box<i32> = (*(*a).x).x;
    let _y: i32 = (*a).y;
}

fn move_after_move_nested() {
    let a: Box<D> = Box::new(D { x: Box::new(A { x: Box::new(0), y: 1 }), y: Box::new(2) });
    let _x: Box<i32> = (*(*a).x).x;
    let _y: Box<i32> = (*a).y;
}

fn borrow_after_move_nested() {
    let a: Box<C> = Box::new(C { x: Box::new(A { x: Box::new(0), y: 1 }), y: 2 });
    let _x: Box<i32> = (*(*a).x).x;
    let _y: &i32 = &(*a).y;
}

fn move_after_borrow_nested() {
    let a: Box<D> = Box::new(D { x: Box::new(A { x: Box::new(0), y: 1 }), y: Box::new(2) });
    let _x: &Box<i32> = &(*(*a).x).x;
    let _y: Box<i32> = (*a).y;
    let _u1: &Box<i32> = _x;
}

fn copy_after_mut_borrow_nested() {
    let mut a: Box<C> = Box::new(C { x: Box::new(A { x: Box::new(0), y: 1 }), y: 2 });
    let _x: &mut Box<i32> = &mut (*(*a).x).x;
    let _y: i32 = (*a).y;
    let _u1: &mut Box<i32> = _x;
}

fn move_after_mut_borrow_nested() {
    let mut a: Box<D> = Box::new(D { x: Box::new(A { x: Box::new(0), y: 1 }), y: Box::new(2) });
    let _x: &mut Box<i32> = &mut (*(*a).x).x;
    let _y: Box<i32> = (*a).y;
    let _u1: &mut Box<i32> = _x;
}

fn borrow_after_mut_borrow_nested() {
    let mut a: Box<C> = Box::new(C { x: Box::new(A { x: Box::new(0), y: 1 }), y: 2 });
    let _x: &mut Box<i32> = &mut (*(*a).x).x;
    let _y: &i32 = &(*a).y;
    let _u1: &mut Box<i32> = _x;
}

fn mut_borrow_after_borrow_nested() {
    let mut a: Box<C> = Box::new(C { x: Box::new(A { x: Box::new(0), y: 1 }), y: 2 });
    let _x: &Box<i32> = &(*(*a).x).x;
    let _y: &mut i32 = &mut (*a).y;
    let _u1: &Box<i32> = _x;
}

fn main() {
    copy_after_move();
    move_after_move();
    borrow_after_move();
    move_after_borrow();
    copy_after_mut_borrow();
    move_after_mut_borrow();
    borrow_after_mut_borrow();
    mut_borrow_after_borrow();
    copy_after_move_nested();
    move_after_move_nested();
    borrow_after_move_nested();
    move_after_borrow_nested();
    copy_after_mut_borrow_nested();
    move_after_mut_borrow_nested();
    borrow_after_mut_borrow_nested();
    mut_borrow_after_borrow_nested();
}
