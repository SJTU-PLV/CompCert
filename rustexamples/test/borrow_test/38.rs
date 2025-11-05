// Find an example to illustrate the effect of function call
// rustc +nightly 38.rs -Z polonius=next

// The following example is too compilcated
fn test1<'a,'b,'c,'d>(mut q: &'a mut &'b mut i32, mut p1: &'c mut i32, mut p2: &'d mut i32) 
    where 'c: 'b, 'd: 'b{
        if true {
            *q = p1;
        } else {
            *q = p2;
        }
}

fn test2<'a,'b,'c>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32
    where 'a: 'c, 'b: 'c{
        if true {
            return a;
        } else {
            return b;
        }
}


// fn test<'a,'b,'c,'d>(mut q: &'a mut &'b mut i32, mut p: &'c mut i32) {
//     q = &mut p;
// }
fn main(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut p = &mut v1; // p1: &mut i32
    test1(&mut p, &mut v2, &mut v3);
//  v1 = 5;
    *p = 4;
}