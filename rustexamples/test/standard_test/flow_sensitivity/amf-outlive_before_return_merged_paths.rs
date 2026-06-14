// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (outlive_before_return_does_not_affect_merged_paths test)

fn reborrow<'a>(a: &'a mut i32) -> &'a mut i32 {
    let b: &mut i32 = &mut *a;
    if true {
        return b;
    } else {
        // loan remains live only in the other branch
    }
    // Outlives constraint from the return path should not propagate here
    let c: &mut i32 = &mut *a;
    return c;
}

fn main() {
    let mut val: i32 = 42;
    let _: &mut i32 = reborrow(&mut val);
}
