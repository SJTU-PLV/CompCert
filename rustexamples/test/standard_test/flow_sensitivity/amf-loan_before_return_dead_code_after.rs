// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (loan_before_return_does_not_affect_dead_code_after test)

fn reborrow<'a>(a: &'a mut i32) -> &'a mut i32 {
    let b: &mut i32 = &mut *a;
    return b;
    // Dead code after return — its borrow should not conflict with the return
    let _c: &mut i32 = &mut *a;
    return _c;
}

fn main() {
    let mut val: i32 = 42;
    let _: &mut i32 = reborrow(&mut val);
}
