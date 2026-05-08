fn test<'a, 'b, 'c, 'd>(x: &'a &'b i32, y: &'c &'d i32) {}

// rustc +nightly 51_callsite_invariance.rs -Z polonius=next 
fn main(){
    let mut x: i32 = 0;
    let mut p: &i32 = & x;
    let mut q1: & &i32 = & p;
    let mut q2: & &i32 = & *q1;
    test(q1, q2); // We do not allow establish invariant for generic regions for now
}