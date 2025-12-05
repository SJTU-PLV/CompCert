//rustc +nightly 36.rs -Z polonius=next

fn main(){
    let v1: i32 = 1;
    let v2: i32 = 2;
    let p1: &i32 = &v1;
    let p2: &i32 = &v2;
    let q : & & i32;
    if true {
        q = &p1;
    } else {
        q = &p2;
    }
    // println!("{}", **q); // make sure q is live
    let tmp: i32 = **q;
    v1 = 2; // Use *p2 (i.e., v2) at the next line should not interfere with the use of v1
    tmp = *p2;
    // println!("{}", *p2);

}