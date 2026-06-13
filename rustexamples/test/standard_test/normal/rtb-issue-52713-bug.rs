// Source: borrowck/issue-52713-bug.rs
// Regression test for a bug in #52713: this was an optimization for
// computing liveness that wound up accidentally causing the program
// below to be accepted.

fn foo<'a>(x: &'a mut i32) -> i32 {
    let mut x2: i32 = 22;
    let y: &i32 = &x2;
    if false {
        return x2;
    }

    x2 = x2 + 1; //~ ERROR
    let _u1: &i32 = y;
    return 0;
}

fn main() {
    let mut val: i32 = 0;
    let _u1: i32 = foo(&mut val);
}
