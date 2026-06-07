// Source: borrowck.rs (use_of_moved_variable test)

struct Datum { value: i32 }

fn main() {
    let x: Datum = Datum { value: 1 };
    let _y: Datum = x;
    let _z: Datum = x; //~ ERROR use of moved value
}
