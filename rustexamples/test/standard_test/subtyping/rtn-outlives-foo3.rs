// Source: nll/outlives-suggestion-simple.rs
// Swapped lifetime pair: each return position fails

fn foo3<'a, 'b>(x: &'a i32, y: &'b i32, out1: &mut &'b i32, out2: &mut &'a i32) {
    *out1 = x; //~ ERROR lifetime may not live long enough
    *out2 = y; //~ ERROR lifetime may not live long enough
}

fn main() {
    let a: i32 = 1;
    let b: i32 = 2;
    let mut r1: &i32 = &a;
    let mut r2: &i32 = &b;
    foo3(&a, &b, &mut r1, &mut r2);
    let _u1: &i32 = r1;
    let _u2: &i32 = r2;
}
