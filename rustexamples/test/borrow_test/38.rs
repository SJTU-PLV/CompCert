// Find an example to illustrate the effect of function call
// rustc +nightly 38.rs -Z polonius=next

// The following example is too compilcated
fn test1<'a,'b,'c,'d>(q: &'a mut &'b mut i32, p1: &'c mut i32, p2: &'d mut i32) 
    where 'c: 'b, 'd: 'b{
        if true {
            *q = p1;
        } else {
            *q = p2;
        }
}

fn test2<'a,'b,'c>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32
    where 'a: 'c, 'b: 'c{
        if *a > *b {
            return &mut *a;
        } else {
            return &mut *b;
        }
}


// fn test<'a,'b,'c,'d>(mut q: &'a mut &'b mut i32, mut p: &'c mut i32) {
//     q = &mut p;
// }
// fn main(){
//     let v1: i32 = 1;
//     let v2: i32 = 2;
//     let v3: i32 = 3;
//     let p: &mut i32 = &mut v1; // p1: &mut i32
//     test1(&mut p, &mut v2, &mut v3);
// //  v1 = 5;
//     *p = 4;
// }

fn main(){
    let v1: i32 = 1;
    let v2: i32 = 2;
    let p: &mut i32 = test2(&mut v1, &mut v2);
//    v1 = 3;
    *p = 4;
}