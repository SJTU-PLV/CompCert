// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (move_out_of_mut_ref test)

struct Datum { value: i32 }

fn main() {
    let mut x: Datum = Datum { value: 1 };
    let r: &mut Datum = &mut x;
    let _y: Datum = *r; //~ ERROR cannot move out of `*r` which is behind a mutable reference
}
