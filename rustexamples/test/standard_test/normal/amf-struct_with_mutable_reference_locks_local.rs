// Source: borrowck.rs (struct_with_mutable_reference_locks_local test)

struct Wrapper<'a> { value: &'a mut i32 }

fn main() {
    let mut v1: i32 = 0;
    let w: Wrapper = Wrapper { value: &mut v1 };
    v1 = 1; //~ ERROR cannot assign to `v1` because it is borrowed
    let _: i32 = *(w.value);
}
