fn main(){
    let v: i32 = 1;
    let dummy1: i32 = 2;
    let dummy2: i32 = 2;
    let p: &mut i32 = &mut dummy1;
    let q: &mut i32 = &mut dummy2;
    if true {
        p = &mut v;
    }
    else{
        q = &mut v;
    }
    v = 4;
    printf("%d", *p);

}

// error[E0506]: cannot assign to `v` because it is borrowed
//   --> src/main.rs:13:5
//    |
// 8  |         p = &mut v;
//    |             ------ `v` is borrowed here
// ...
// 13 |     v = 4;
//    |     ^^^^^ `v` is assigned to here but it was already borrowed
// 14 |     println!("{}", *p);
//    |                    -- borrow later used here