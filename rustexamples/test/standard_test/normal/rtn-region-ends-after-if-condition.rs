// Repo: rust-lang/rust
// Source: nll/region-ends-after-if-condition.rs
// Borrow in if-condition ends before else branch — mutation in else is OK

fn foo1() {
    let mut x: i32 = 0;
    let value: &i32 = &x;
    if *value == 0 {
        let _u1: i32 = *value; // borrow still active
    }
    // borrow ended after if — mutation is OK
    x = 1;
    let _u2: i32 = x;
}

fn foo2() {
    let mut x: i32 = 0;
    let value: &i32 = &x;
    if *value == 0 {
        x = 1; //~ ERROR E0506 cannot assign to `x` because it is borrowed
        let _u1: i32 = *value;
    }
    let _u2: i32 = *value;
}

fn main() {
    foo1();
    foo2();
}
