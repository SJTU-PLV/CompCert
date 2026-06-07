// Source: borrowck.rs (move_whole_then_access_field test)

struct Datum { value: i32 }

struct Pair { first: Datum, second: Datum }

fn main() {
    let x: Pair = Pair { first: Datum { value: 1 }, second: Datum { value: 2 } };
    let _a: Pair = x;
    let _b: Datum = x.first; //~ ERROR use of moved value: `x.first`
}
