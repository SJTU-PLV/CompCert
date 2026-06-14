// Source: nll/issue-48803.rs
// Borrow chain through flatten prevents mutation

fn flatten<'a, 'b>(x: &'a &'b i32) -> &'a i32 {
    return *x;
}

fn main() {
    let val: i32 = 1;
    let mut x: &i32 = &val;
    let y: & &i32 = &x;
    let z: & & &i32 = &y;
    let w: &i32 = flatten(z);
    x = &val; //~ ERROR cannot assign to `x` because it is borrowed [E0506]
    let _u1: &i32 = w;
}
