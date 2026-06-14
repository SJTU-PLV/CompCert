// Repo: rust-lang/rust
// Source: borrowck/borrowck-match-already-borrowed.rs
// E0503: cannot use variable in match because it is mutably borrowed

enum Foo {
    A(i32),
    B
}

fn match_enum() {
    let mut foo: Foo = Foo::B;
    let p: &mut Foo = &mut foo;
    let _val: i32;
    match foo { //~ ERROR cannot use `foo` because it was mutably borrowed
        Foo::B => { _val = 1; }
        _ => { _val = 2; }
    };
    let _u1: &mut Foo = p;
}

fn match_i32() {
    let mut x: i32 = 1;
    let r: &mut i32 = &mut x;
    let _val: i32;
    match x { //~ ERROR cannot use `x` because it was mutably borrowed
        y => { _val = y + 1; }
    };
    let _u1: &mut i32 = r;
}

fn main() {
    match_enum();
    match_i32();
}
