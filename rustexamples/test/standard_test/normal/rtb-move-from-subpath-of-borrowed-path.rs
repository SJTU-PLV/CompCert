// Source: borrowck/borrowck-move-from-subpath-of-borrowed-path.rs
// verify that an error is raised when trying to move out of a
// borrowed path.



fn main() {
    let a: Box<Box<i32>> = Box::new(Box::new(2));
    let b: &Box<Box<i32>> = &a;

    let z: Box<i32> = *a; //~ ERROR: cannot move out of `*a` because it is borrowed
    let _u1: &Box<Box<i32>> = b;
    let _u2: Box<i32> = z;
}
