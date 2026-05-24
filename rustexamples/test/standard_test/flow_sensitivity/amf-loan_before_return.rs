// Source: borrowck.rs (loan_before_return_does_not_affect_merged_paths test)

fn reborrow(a: &mut i32) -> &mut i32 {
    if true {
        let b: &mut i32 = &mut *a;
        return b;
    } else { }

    let c: &mut i32 = &mut *a;
    return c;
}

fn main() {
    let mut val: i32 = 5;
    let result: &mut i32 = reborrow(&mut val);
    *result = 10;
    let _: i32 = val;
}
