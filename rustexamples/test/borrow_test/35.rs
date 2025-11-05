//rustc +nightly 35.rs -Z polonius=next

fn main(){
    let mut v1 = 1;
    let mut v2 =2;
    let mut p = &mut v1;
    let mut q = &mut p;
    let mut b = Box::new(&mut *q); //&mut *q has type &mut &mut i32, so b has type Box<&'a mut &'b mut i32> and 'b is equal to 'q2
    **b = &mut v2;   
    v2 = 3;
    *p = 4;
}