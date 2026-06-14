// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (break_drops_borrowed_local test)

fn main() {
    let r: &i32;
    loop {
        let x: i32 = 0;
        r = &x; // borrow x
        break; // drops x while r is still live
    }
    let _: i32 = *r; //~ ERROR `x` does not live long enough
}
