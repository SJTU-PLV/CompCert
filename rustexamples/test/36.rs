//rustc +nightly 36.rs -Z polonius=next

// We do not suppor covariant for nested share reference, so this test
// case cannot be compiled by our compiler but can be compiled by
// rustc with Polonius.

fn main(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut p1: &i32 = &v1;
    let mut p2: &i32 = &v2;
    let mut q : & & i32;
    if true {
        q = &p1;
    } else {
        q = &p2;
    }
    // println!("{}", **q); // make sure q is live
    let mut tmp: i32 = **q;
    v1 = 2; // Use *p2 (i.e., v2) at the next line should not interfere with the use of v1
    tmp = *p2;
    // println!("{}", *p2);

}