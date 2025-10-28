fn main(){
    let mut v = 12;
    let mut dummy1 = 13;
    let mut dummy2 = 13;
    let mut dummy_q1 = &mut dummy1;
    let mut dummy_q2 = &mut dummy2;
    let mut p = &mut v;
    let mut q1 = &mut dummy_q1;
    let mut q2 = &mut dummy_q2;
    if true {
        q1 = &mut p;
    } else {
        q2 = &mut p;
    }
    **q1 = 15;
    **q2 = 20;
    **q1 = 15;
}
// The borrow checker can judge that **q1 and **q2 are not aliased， but their regions are invariant?

//rustc +nightly 31.rs -Z polonius=next