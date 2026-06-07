// Source: borrowck.rs (mutable_ref_prevents_mutation test)

fn main() {
    let mut i: i32 = 0;
    let j: &mut i32 = &mut i;
    i = 1; //~ ERROR cannot assign to `i` because it is borrowed
    let _: i32 = *j;
}
