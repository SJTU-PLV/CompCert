// Source: borrowck/borrowck-bad-nested-calls-free.rs
// Nested calls that free pointers: immutable borrow of `a` for first arg
// conflicts with mutable borrow of `a` in second arg

fn rewrite(v: &mut Box<i32>) -> i32 {
    *v = Box::new(22);
    return **v;
}

fn add(v: &i32, w: i32) -> i32 {
    return *v + w;
}

fn implicit() {
    let mut a: Box<i32> = Box::new(1);
    let _u1: i32 = add(
        &*a,
        rewrite(&mut a)); //~ ERROR cannot borrow
}

fn explicit() {
    let mut a: Box<i32> = Box::new(1);
    let _u1: i32 = add(
        &*a,
        rewrite(&mut a)); //~ ERROR cannot borrow
}

fn main() {
    implicit();
    explicit();
}
