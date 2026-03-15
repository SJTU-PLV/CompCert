// Current Polonius
// let mut v: i32 = 1;
// let p: &'p mut i32 = &'v mut v;
// v = 2; // Current Polonius reports error here: 
//        // 'p is live origin computed by liveness analysis, 
//        // so v is a live loan and accessing v is invalid
// ... // unrelated code
// *p = 3;

// // Pure forward propagation
// let mut v: i32 = 1;
// let p: &'p mut i32 = &'v mut v;
// v = 2; // no error report here; accessing v would invalidate the origin 'p as {v} ⊆ 'p
// ... // unrelated code
// *p = 3; // In pure forward propagation: 
//         // the error is reported here because using *p would access invalid origin 'p


// fn main(){
//     let mut v1: i32 = 1;
//     let mut v2: i32 = 2;
//     let mut p1: & 'p1 mut i32 = & 'v1 mut v1; 
//         // 'p1: {v1}
//     let mut p2: & 'p2 mut i32 = & 's_p1 mut *p1; 
//         // 'p1: {v1}, 'p2: {*p1, v1}
//     p1 = &'v2 mut v2; // 'p1: {v2}, 'p2: {v1}
//     *p1 = 3; // 'p1: {}, 'p2: {v1}
//     *p2 = 4; // 'p1: {}, 'p2: {v1}

//     v2 = 5; // 'p1: {}, 'p2: {v1}

//     v1 = 6; // 'p1: {}, 'p2: {v1}
//     println!("{}", *p2); // 'p1: {}, 'p2: {v1}
// }

// fn main(){
//     let mut v1: i32 = 1;
//     let mut v2: i32 = 2;
//     let mut p1: & 'p1 mut i32 = & 'v1 mut v1; 
//         // after this point: live loans is {v1}
//     let mut p2: & 'p2 mut i32 = & 's_p1 mut *p1; 
//         // live loans is {v1, *p1}
//     p1 = &'v2 mut v2; // {v1, v2}
//     *p1 = 3; // {v1}
//     *p2 = 4; // {v1}

//     v2 = 5; // {v1}

//     v1 = 6; 
//         // {v1}: Error! we use v1 but v1 is in the set of live loans!
//     println!("{}", *p2); // {}
// }

// // The syntax is not supported in our compiler
// // rustc +nightly -Z polonius 28.rs
// fn main(){
//     let mut v1: i32 = 1;
//     let mut v2: i32 = 2;
//     let mut p1: & 'p1 mut i32 = & 'v1 mut v1; 
//         // {v1} ⊆ 'v1, 'v1 ⊆ 'p1
//     let mut p2: & 'p2 mut i32 = & 's_p1 mut *p1; 
//         // {*p1} ⊆ 's_p1, 'p1 ⊆ 's_p1, 's_p1 ⊆ 'p2
//     p1 = &'v2 mut v2; // {v2} ⊆ 'v2, 'v2 ⊆ 'p1
//     *p1 = 3;
//     *p2 = 4;

//     v2 = 5;

//     v1 = 6;
//     println!("{}", *p2);
// }


// fn main(){
//     let mut v1: i32 = 1;
//     let mut v2: i32 = 2;
//     let mut p1: &mut i32 = &mut v1;
//     let mut p2: &mut i32 = &mut *p1;
//     p1 = &mut v2;
//     *p1 = 3;
//     *p2 = 4;

//     v2 = 5;

//     v1 = 6;
//     println!("{}", *p2);
// }

fn main(){
    let v1: i32 = 1;
    let v2: i32 = 2;
    let p1: & mut i32 = & mut v1; 
        // after this point: live loans is {v1}
    let p2: & mut i32 = & mut *p1; 
        // live loans is {v1, *p1}
    p1 = &mut v2; // {v1, v2}
    *p1 = 3; // {v1}
    *p2 = 4; // {v1}

    v2 = 5; // {v1}

    v1 = 6; // {v1}
    // println!("{}", *p2); // {}
}
