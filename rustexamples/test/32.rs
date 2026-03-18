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
    let mut v1 : i32 = 22;
    let mut v2 : i32 = 44;
    let mut p1: &mut i32 = &mut v1; // ['p1] -> {v1}
    let mut p2: &mut i32 = &mut v2; // ['p1] -> {v1}, ['p2] -> {v2}
    let mut q: &mut &mut i32 = &mut p1; // ['q1] -> {p1}, ['p1, 'q2] -> {v1}, ['p2] -> {v2}
    if true {
        // Steps of transfer in line :
        // 1. apply liveness: remove 'q1 and 'q2 as q1 is dead, which produces ['p1] -> {v1}, ['p2] -> {v2}
        // 2. access *p1 mutably: OK because *p1 is not an active loan
        // 3. apply liveness: remove 'p1 as p1 is dead after this line, which produces ['p2] -> {v2} (TODO: we should talk about why we need this liveness application after the main transfer)
        *p1 = 3; // ['p2] -> {v2}
        q = &mut p2; // ['q1] -> {p2}, ['q2, 'p2] -> {v2}
    } else {
        *q = &mut *p2; // ['q1] -> {p1}, ['p1, 'q2] -> {v1, v2, *p2}, ['p2] -> {v2}
    } // 'q1 -> {p1, p2}, ['p1, 'p2, 'q2] -> {v1, v2, *p2}
    v1 = 13; // 'q1 -> {p1, p2}, ['p1, 'p2, 'q2] -> Invalid
             // After this line, using places containing one of 'p1, 'p2 and 'q2 would cause error
    *p1 = 3;
    *p2 = 3;

}


fn test(){
    let mut v1 : i32 = 22;
    let mut v2 : i32 = 44;
    let mut p1: &mut i32 = &mut v1; // ['p1] -> {v1}
    let mut p2: &mut i32 = &mut v2; // ['p1] -> {v1}, ['p2] -> {v2}
    let mut q: &mut &mut i32 = &mut p1; // ['q1] -> {p1}, ['p1, 'q2] -> {v1}, ['p2] ->  {v2}
    if true {
        q = &mut p2;
    }
    else {
        *q = &mut v2;
        p2 = &mut v1;
    }
}
