// Repo: rust-lang/polonius
// Source: inputs/smoke-test/polonius-smoke-test.rs (move_reinitialize_ok test)

struct Datum { value: i32 }

fn main() {
    let mut x: Datum = Datum { value: 1 };
    let y: Datum = x; // move x into y
    x = Datum { value: 2 }; // reinitialize x
    let _a: i32 = x.value; // OK — x has been reinitialized
    let _b: i32 = y.value;
}
