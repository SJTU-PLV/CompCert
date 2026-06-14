// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (assign_field_of_uninitialized test)

struct Pair { first: i32, second: i32 }

fn main() {
    let x: Pair;
    x.first = 1; //~ ERROR assign to field of uninitialized variable
}
