// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (partial_move_use_sibling test)

struct Datum { value: i32 }

struct Pair { first: Datum, second: Datum }

fn main() {
    let x: Pair = Pair { first: Datum { value: 1 }, second: Datum { value: 2 } };
    let _a: Datum = x.first;
    let _b: Datum = x.second; // OK, sibling still accessible after partial move
}
