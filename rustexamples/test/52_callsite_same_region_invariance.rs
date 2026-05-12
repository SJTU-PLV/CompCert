fn test_error<'a, 'b, 'c>(mut x: &'a mut &'c mut i32, mut y: &'b mut &'c mut i32) {}
fn test_ok<'a, 'b, 'c, 'd>(mut x: &'a mut &'c mut i32, mut y: &'b mut &'d mut i32) {}

// rustc +nightly 52_callsite_same_region_invariance.rs -Z polonius=next 
fn main()
{
    let mut v1: i32 = 0;
    let mut v2: i32 = 0;
    let mut p: &mut i32 = &mut v1;
    let mut q: &mut i32 = &mut v2;
    test_error(&mut p, &mut q); // 'p1 = 'c and 'p2 = 'c so 'p1 = 'p2
    // v1 = 2; // error here because we unify p and q
    *q = 3;
}