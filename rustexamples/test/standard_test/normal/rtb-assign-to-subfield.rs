// Repo: rust-lang/rust
// Source: borrowck/borrowck-assign-to-subfield.rs

struct A {
    a: i32,
    w: B
}
struct B {
    a: i32
}

fn main() {
    let mut p: A = A {
        a: 1,
        w: B { a: 1 }
    };

    // even though `x` is not declared as a mutable field,
    // `p` as a whole is mutable, so it can be modified.
    p.a = 2;

    // this is true for an interior field too
    p.w.a = 2;

    let _u1: i32 = p.a;
    let _u2: i32 = p.w.a;
}
