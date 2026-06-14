// Repo: rust-lang/rust
// Source: borrowck/borrowck-anon-fields-variant.rs
// Enum variant borrow: borrowing one field of a variant blocks all access

struct FooY { a: i32, b: i32 }

enum Foo {
    X,
    Y(FooY)
}

fn distinct_variant() {
    let mut y: Foo = Foo::Y(FooY { a: 1, b: 2 });
    let a: &mut i32;
    match y {
        Foo::Y(ref mut ys) => { a = &mut ys.a; }
        Foo::X => { loop {} }
    };
    let b: &mut i32;
    match y { //~ ERROR cannot use `y`
        Foo::Y(ref mut ys2) => { b = &mut ys2.b; }
        Foo::X => { loop {} }
    };
    *a = *a + 1;
    *b = *b + 1;
}

fn same_variant() {
    let mut y: Foo = Foo::Y(FooY { a: 1, b: 2 });
    let a: &mut i32;
    match y {
        Foo::Y(ref mut ys) => { a = &mut ys.a; }
        Foo::X => { loop {} }
    };
    let b: &mut i32;
    match y { //~ ERROR cannot use `y`
        Foo::Y(ref mut ys2) => { b = &mut ys2.a; } //~ ERROR cannot borrow
        Foo::X => { loop {} }
    };
    *a = *a + 1;
    *b = *b + 1;
}

fn main() {
    distinct_variant();
    same_variant();
}
