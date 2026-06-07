// Source: borrowck.rs (call_pass_ref test)

fn foo<'a>(x: &'a i32) -> i32 {
    return *x;
}

fn main() {
    let v: i32 = 7;
    let r: i32 = foo(&v);
    let _a: i32 = r;
    let _b: i32 = v;
}
