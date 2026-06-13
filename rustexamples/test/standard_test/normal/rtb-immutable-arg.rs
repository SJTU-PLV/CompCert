// Source: borrowck/immutable-arg.rs

fn foo(x: i32) {
    x = 1; //~ ERROR E0384 cannot assign to immutable argument
}

fn main() {
    foo(0);
}
