// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (drop_on_break_while_borrowed test)

fn main() {
    let v2: &i32;
    {
        let v1: i32 = 0;
        v2 = &v1;
        break; // break exits 'a, dropping v1 — ERROR, v1 still borrowed
    }
    let _: i32 = *v2;
}
