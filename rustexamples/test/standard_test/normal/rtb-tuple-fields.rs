// Repo: rust-lang/rust
// Source: borrowck/borrow-tuple-fields.rs
// Removed: tuple-based tests (tuples unsupported), kept struct-based tests.

struct Foo { x: Box<i32>, y: i32 }
struct Bar { x: i32, y: i32 }

fn main() {
    let x1: Foo = Foo { x: Box::new(1), y: 2 };
    let r: &Box<i32> = &x1.x;
    let y: Foo = x1; //~ ERROR cannot move out of `x1` because it is borrowed
    let _u1: Foo = y;
    let _u2: &Box<i32> = r;

    let mut x2: Bar = Bar { x: 1, y: 2 };
    let a1: &i32 = &x2.x;
    let b1: &mut i32 = &mut x2.x; //~ ERROR cannot borrow `x2.x` as mutable because it is also borrowed as
    let _u3: &i32 = a1;
    let _u4: &mut i32 = b1;

    let mut x3: Bar = Bar { x: 1, y: 2 };
    let a2: &mut i32 = &mut x3.x;
    let b2: &mut i32 = &mut x3.x; //~ ERROR cannot borrow `x3.x` as mutable more than once at a time
    let _u5: &mut i32 = a2;
    let _u6: &mut i32 = b2;
}
