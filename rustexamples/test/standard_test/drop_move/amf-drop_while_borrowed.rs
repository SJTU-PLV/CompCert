// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (drop_while_borrowed test)

fn main() {
    let v2: &i32;
    {
        let v1: i32 = 0;
        v2 = &v1;
    } // v1 drops here — ERROR, still borrowed
    let _: i32 = *v2;
}
