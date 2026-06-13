// Source: borrowck/borrowck-assign-comp.rs
// Multiple scenarios of struct borrow vs. assignment conflicts

struct Point { x: i32, y: i32 }

fn a() {
    let mut p: Point = Point { x: 3, y: 4 };
    let q: &Point = &p;

    // This assignment is illegal because the field x is not
    // inherently mutable; since `p` was made immutable, `p.x` is now
    // immutable. Otherwise the type of `q.x` (&i32) would be wrong.
    p.x = 5; //~ ERROR cannot assign to `p.x` because it is borrowed
    let _u1: i32 = q.x;
}

fn c() {
    // this is sort of the opposite. We take a loan to the interior of `p`
    // and then try to overwrite `p` as a whole.

    let mut p: Point = Point { x: 3, y: 4 };
    let q: &i32 = &p.y;
    p = Point { x: 5, y: 7 }; //~ ERROR cannot assign to `p` because it is borrowed
    let _u1: i32 = p.x;
    let _u2: i32 = *q;
}

fn d() {
    // just for completeness's sake, the easy case, where we take the
    // address of a subcomponent and then modify that subcomponent:

    let mut p: Point = Point { x: 3, y: 4 };
    let q: &i32 = &p.y;
    p.y = 5; //~ ERROR cannot assign to `p.y` because it is borrowed
    let _u1: i32 = *q;
}

fn main() {
    a();
    c();
    d();
}
