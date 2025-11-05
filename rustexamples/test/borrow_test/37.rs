// reborrow of field
// rustc +nightly 37.rs -Z polonius=next

struct pair {
    first: i32,
    second: i32,
}

fn main(){
    let p: pair;
    p.first = 12;
    p.second = 14;
    let x: &mut pair = &mut p;
    let y: &mut i32 = &mut (*x).first;
    p.second = 15; // It should not be error
    *y = 20;
}

// fn main(){
//     let mut p: pair;
//     p.first = 12;
//     p.second = 14;
//     let mut x: &mut pair = &mut p;
//     let mut y: &mut i32 = &mut (*x).first;
//     p.second = 15; // Polonius report error here: p.second` is assigned to here but it was already borrowed
//     *y = 20;
// }