// Source: borrowck/issue-45199.rs
// E0384: cannot assign twice to immutable variable of Box type

fn test_drop_replace() {
    let b: Box<i32>;
    b = Box::new(1);
    b = Box::new(2); //~ ERROR cannot assign twice to immutable variable `b`
}

fn test_call() {
    let b: Box<i32> = Box::new(1);
    b = Box::new(2); //~ ERROR cannot assign twice to immutable variable `b`
}

fn test_args(b: Box<i32>) {
    b = Box::new(2); //~ ERROR cannot assign to immutable argument `b`
}

fn main() {
    test_drop_replace();
    test_call();
    test_args(Box::new(1));
}
