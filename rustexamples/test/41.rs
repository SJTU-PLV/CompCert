
//rustc +nightly 41.rs -Z polonius=next
fn main(){
    let v: i32 = 12;
    let v1: i32 = 13;
    let p: &mut i32 = &mut v;
    let p1: &mut &mut i32 = &mut p;
    let p2: &mut &mut i32 = &mut *p1;
    let q: &mut i32 = &mut v1;
    *p2 = &mut *q;
    v = 4; // error here
    **p1 = 13; 
}
