// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (struct_construction_with_borrowed_local test)

struct Wrapper { value: i32 }

fn main() {
    let mut v1: i32 = 22;
    let v2: &mut i32 = &mut v1;
    let w: Wrapper = Wrapper { value: v1 }; //~ ERROR cannot use `v1` because it is borrowed
    let _: i32 = *v2;
}
