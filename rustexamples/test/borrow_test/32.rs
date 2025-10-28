//rustc +nightly 32.rs -Z polonius=next

// fn cond() -> bool {
//     return true;
// }

// fn unrelated() {
//     let mut n = 1;
//     while n < 100 {
//         n += 1;
//     }
// }

fn main(){
    let v1 : i32 = 22;
    let v2 : i32 = 44;
    let p2: &mut i32 = &mut v2; // 'p2 -> {v2}
    let p1: &mut i32 = &mut v1; // 'p1 -> {v1}, 'p2 -> {v2}
    let q1: &mut &mut i32 = &mut p1; // 'q1 -> {p1}, ['p1, 'q2] -> {v1}, 'p2 -> {v2}
    if true {
        *p1 = 3; // 'q1 -> Invalid, ['p1, 'q2] -> {v1}, 'p2 -> {v2}
        // p2 = &mut v2; // we cannot put p2 early because &mut v2 in the else branch would invalidate p2
        q1 = &mut p2; // 'q1 -> {p2}, ['q2, 'p2] -> {v2}, 'p1 -> {v1}
    } else {
        *q1 = &mut *p2; // 'q1 -> {p1}, ['p1, 'q2] -> {v1, v2, *p2}, 'p2 -> {v2}
        // v1 = 13;
        // *p1 = 5;
    } // 'q1 -> {p1, p2}, ['p1, 'p2, 'q2] -> {v1, v2, *p2}
    v1 = 13; // 'q1 -> {p1, p2}, ['p1, 'p2, 'q2] -> Invalid
             // After this line, using places containing one of 'p1, 'p2 and 'q2 would cause error
    // *p1 = 3;
    *p2 = 3;
     **q1 = 5;
    *p2 = 5; // error
    **q1 = 3; // error
}
