// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (call_mut_under_shared_borrow test)

fn foo(x: &mut i32) -> i32 {
    *x = 1;
    return 1;
}

fn main() {
    let mut v: i32 = 0;
    let p: &i32 = &v;
    let _a: i32 = foo(&mut v); //~ ERROR cannot borrow `v` as mutable because it is also borrowed as immutable
    let _b: i32 = *p;
}
