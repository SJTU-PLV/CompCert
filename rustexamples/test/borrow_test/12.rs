fn main(){
    let v: i32 = 1;
    let dummy1: i32 = 2;
    let dummy2: &mut i32 = &mut dummy1;
    let p: &mut i32 = &mut v;
    let x: &mut &mut i32 = &mut p;
    let tmp: i32 = 2;
    *x = &mut tmp;
    x = &mut dummy2;
    tmp = 3;
    *p = 4; // we report error here
}

// rustc error message:
// error[E0506]: cannot assign to `tmp` because it is borrowed
//   --> src/main.rs:10:5
//    |
// 8  |     *x = &mut tmp;
//    |          -------- `tmp` is borrowed here
// 9  |     x = &mut dummy2;
// 10 |     tmp = 3;
//    |     ^^^^^^^ `tmp` is assigned to here but it was already borrowed
// 11 |     *p = 4;
//    |     ------ borrow later used here