// Source: borrowck/borrowck-borrow-immut-deref-of-box-as-mut.rs

struct A {
    x: i32
}

fn foo(a: &mut A) {
}

fn main() {
    let a: Box<A> = Box::new(A { x: 0 });
    foo(&mut *a);
    //~^ ERROR cannot borrow `*a` as mutable, as `a` is not declared as mutable [E0596]
}
