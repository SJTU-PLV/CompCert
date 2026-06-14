// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (reinit_after_move test)

struct Datum { value: i32 }

fn main() {
    let x: Datum = Datum { value: 1 };
    let _y: Datum = x;
    x = Datum { value: 2 }; // re-init, OK
    let _z: Datum = x;
}
