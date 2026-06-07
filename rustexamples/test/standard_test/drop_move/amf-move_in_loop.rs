// Source: borrowck.rs (move_in_loop test)

struct Datum { value: i32 }

fn main() {
    let x: Datum = Datum { value: 1 };
    loop {
        let _y: Datum = x; //~ ERROR use of moved value: `x`
    }
}
