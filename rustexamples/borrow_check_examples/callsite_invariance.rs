use std::cell::Cell;

// fn test<'a>(x: &'a mut i32) {
//     let mut v: i32 = 1;
//     x = &mut v; // 'a: {v}
//     v = 3;
// }

fn test2<'a, 'b, 'c: 'a>(x: &Cell<&'a i32>, y: &Cell<&'b i32>, z: &'c mut i32) {
    // let mut v: i32 = 1;
    x.set(& *z); // 'a: {v}
    // v = 3;

}

// rustc +nightly callsite_invariance.rs -Z polonius=next 

fn main(){
    let mut x: i32 = 0;
    let mut p: &i32 = & x;
    let mut c: &Cell<&i32> = &Cell::new(p); // c: &'c1 Cell<&'c2 i32>
    let mut d: &Cell<&i32> = &*c; // d2 = c2
    let mut y: i32 = 1;
    test2(c, d, &mut y); // c2 = 'a, d2 = 'b so 'a = 'b but this relation is not expressed in test2. Polonius thinks it is ok
    y = 3;
    println!("{}", *d.get());
}