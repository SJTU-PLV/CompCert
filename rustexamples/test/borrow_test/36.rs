//rustc +nightly 36.rs -Z polonius=next



fn main(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut p1 = &v1;
    let mut p2 = &v2;
    let mut q: && i32;
    if true {
        q = &p1;
    } else {
        q = &p2;
    }
    println!("{}", **q); // make sure q is live
    v1 = 2; // It would be error if we use mutable references
    println!("{}", *p2);

}

// fn main(){
//     let mut v1 = 1;
//     let mut v2 = 2;
//     let mut p1 = &mut v1;
//     let mut p2 = &mut v2;
//     let mut q: &mut &mut i32;
//     if true {
//         q = &mut p1;
//     } else {
//         q = &mut p2;
//     }
//     println!("{}", **q); // make sure q is live
//     v1 = 2; // It would be error if we use mutable references
//     println!("{}", *p2);

// }