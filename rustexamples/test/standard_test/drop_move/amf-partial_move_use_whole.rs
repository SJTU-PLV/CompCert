// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (partial_move_use_whole test)

struct Datum { value: i32 }

struct Pair { first: Datum, second: Datum }

fn main() {
    let x: Pair = Pair { first: Datum { value: 1 }, second: Datum { value: 2 } };
    let _a: Datum = x.first;
    let _b: Pair = x; //~ ERROR use of partially moved value: `x`
}
