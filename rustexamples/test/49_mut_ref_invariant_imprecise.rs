//rustc +nightly 49_mut_ref_invariant_imprecise.rs -Z polonius=next

// A variant of 36.rs where we use mutable reference to illustrate the
// imprecision of invariant for mutable reference. Both Polonius and
// our borrow checker reject this program. 

fn main(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut p1: &mut i32 = &mut v1;
    let mut p2: &mut i32 = &mut v2;
    let mut q : &mut & mut i32;
    if true {
        q = &mut p1;
    } else {
        q = &mut p2;
    }
    let mut tmp: i32 = **q;
    v1 = 2; 
    tmp = *p2; // If we uncomment this line, there would be error at the last line
}