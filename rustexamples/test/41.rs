
//rustc +nightly 41.rs -Z polonius=next
fn main(){
    let mut v: i32 = 12;
    let mut v1: i32 = 13;
    let mut p: &mut i32 = &mut v;
    let mut p1: &mut &mut i32 = &mut p;
    let mut p2: &mut &mut i32 = &mut *p1;
    let mut q: &mut i32 = &mut v1;
    *p2 = &mut *q;
    v = 4; // error here
    **p1 = 13; 
}
