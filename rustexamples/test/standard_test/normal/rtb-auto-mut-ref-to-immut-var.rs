// Repo: rust-lang/rust
// Source: borrowck/borrowck-auto-mut-ref-to-immut-var.rs
// Tests that auto-ref can't create mutable aliases to immutable memory.

struct Foo {
    x: i32
}

fn printme(f: &mut Foo) {
    let _u1: i32 = f.x;
}

fn main() {
    let x: Foo = Foo { x: 3 };
    printme(&mut x); //~ ERROR cannot borrow
}
