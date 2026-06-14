// Source: nll/outlives-suggestion-simple.rs
// One input lifetime must satisfy two output lifetimes

fn foo4<'a, 'b, 'c>(x: &'a i32, out1: &mut &'b i32, out2: &mut &'c i32) {
    *out1 = x; //~ ERROR lifetime may not live long enough
    *out2 = x; //~ ERROR lifetime may not live long enough
}

fn main() {
    let val: i32 = 42;
    let mut r1: &i32 = &val;
    let mut r2: &i32 = &val;
    foo4(&val, &mut r1, &mut r2);
    let _u1: &i32 = r1;
    let _u2: &i32 = r2;
}
