// Source: borrowck.rs (move_out_of_borrowed_place test)

struct Datum { value: i32 }

fn main() {
    let x: Datum = Datum { value: 1 };
    let r: &Datum = &x;
    let _y: Datum = x; //~ ERROR cannot move out of `x` because it is borrowed
    let _: i32 = r.value;
}
