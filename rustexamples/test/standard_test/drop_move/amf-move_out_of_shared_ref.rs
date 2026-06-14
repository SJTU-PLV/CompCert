// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (move_out_of_shared_ref test)

struct Datum { value: i32 }

fn main() {
    let x: Datum = Datum { value: 1 };
    let r: &Datum = &x;
    let _y: Datum = *r; //~ ERROR cannot move out of `*r` which is behind a shared reference
}
