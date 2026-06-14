// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (call_while_borrow_live test)

fn foo(x: i32) -> i32 { return x; }

fn main() {
    let v: i32 = 1;
    let p: &i32 = &v;
    let _a: i32 = foo(0);
    let _b: i32 = *p;
}
