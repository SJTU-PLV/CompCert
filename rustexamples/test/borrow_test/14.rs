fn main(){
    let v: i32 = 1;
    let tmp: i32 = 2;
    let p: &mut i32 = &mut v;
    let q: &mut i32 = &mut *p;
    p = &mut tmp; // note that p is reassigned here
    *q = 5;
    v = 4;
    *p = 3; // using p does not affect v
}

// This example can be passed in Polonius, i.e., that our borrow checker is based on. But the NLL reports errors for these case

// error[E0506]: cannot assign to `v` because it is borrowed
//  --> src/main.rs:8:5
//   |
// 4 |     let mut p: &mut i32 = &mut v;
//   |                           ------ `v` is borrowed here
// ...
// 8 |     v = 4;
//   |     ^^^^^ `v` is assigned to here but it was already borrowed
// 9 |     *p = 3;
//   |     ------ borrow later used here