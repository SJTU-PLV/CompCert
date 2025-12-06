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
    // p.second = 15; // It is an error here due to the imprecision of reborrow which considers that x is being borrowed
    *y = 20;
}
