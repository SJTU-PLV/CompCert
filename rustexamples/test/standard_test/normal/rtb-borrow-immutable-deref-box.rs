// Source: borrowck/borrow-immutable-deref-box.rs
// E0596: cannot borrow `*x` as mutable because `x` is an immutable Box

fn f(x: &mut i32) {}

fn main() {
    let x: Box<i32> = Box::new(3);
    f(&mut *x); //~ ERROR cannot borrow `*x` as mutable, as `x` is not declared as mutable
}
