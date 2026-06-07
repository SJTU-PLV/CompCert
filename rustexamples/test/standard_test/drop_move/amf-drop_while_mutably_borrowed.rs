// Source: borrowck.rs (drop_while_mutably_borrowed test)

fn main() {
    let v2: &mut i32;
    {
        let mut v1: i32 = 0;
        v2 = &mut v1;
    } // v1 drops here — ERROR, still mutably borrowed
    let _: i32 = *v2;
}
