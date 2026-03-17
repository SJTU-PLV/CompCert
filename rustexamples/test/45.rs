
// An example coming from the thesis "Formal Verification of Rust
// programs by functional translation", which demonstrates the
// imprecision of reborrow in NLL. It can be checked by our borrow
// checker and Polonius.

fn main(){
    let mut x : i32 = 0;
    let mut px1: &mut i32 = &mut x;
    let mut px2: &mut i32 = &mut *px1;
    let mut y: i32 = 1;
    px1 = &mut y;
    let mut tmp: i32;
    tmp = *px1;
    tmp = *px2;
    tmp = y;
    tmp = *px2;
}