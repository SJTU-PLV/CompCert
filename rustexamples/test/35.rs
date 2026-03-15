//rustc +nightly 35.rs -Z polonius=next

fn main(){
    let v1: i32 = 1;
    let v2: i32 = 2;
    let p: &mut i32 = &mut v1;
    let q: &mut &mut i32 = &mut p;
    let b: Box<&mut &mut i32> = Box(&mut *q); //&mut *q has type &mut &mut i32, so b has type Box<&'a mut &'b mut i32> and 'b is equal to 'q2
    **b = &mut v2;   
    // v2 = 3; // error should be reported here
    *p = 4;
}