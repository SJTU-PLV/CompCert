// The borrow checker can judge that **q1 and **q2 are not aliased， but their regions are invariant?

//rustc +nightly 31.rs -Z polonius=next

fn main(){
    let v: i32 = 12;
    let dummy1: i32 = 13;
    let dummy2: i32 = 13;
    let dummy_q1: &mut i32 = &mut dummy1;
    let dummy_q2: &mut i32 = &mut dummy2;
    let p: &mut i32 = &mut v;
    let q1: &mut &mut i32 = &mut dummy_q1;
    let q2: &mut &mut i32 = &mut dummy_q2;
    if true {
        q1 = &mut p;
    } else {
        q2 = &mut p;
    }
    **q1 = 15;
    **q2 = 20;
    **q1 = 15;
}