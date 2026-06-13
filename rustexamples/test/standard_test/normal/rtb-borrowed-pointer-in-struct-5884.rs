// Source: borrowck/borrowed-pointer-in-struct-5884.rs
// Positive test: struct with Box field and reference field, borrowing through Box

enum MyOption {
    Some(i32),
    None
}

struct Foo {
    a: i32
}

struct Bar<'a> {
    a: Box<MyOption>,
    b: &'a Foo
}

fn check(a: Box<Foo>) {
    let _ic: Bar = Bar { b: &*a, a: Box::new(MyOption::None) };
}

fn main() {
    check(Box::new(Foo { a: 42 }));
}
