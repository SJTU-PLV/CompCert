// fn main() {
//     let mut x: i32 = 0;
//     let mut p: &'p1 mut i32 = &mut x; // 'p: {x}
//     let mut q: &'q1 mut &'q2 mut i32 = &mut p; // 'q1: {p}, ['q2, 'p]: {x}
//     let r: &'r i32 = &**q; // 'r: {**q, p, x}, q1: {p}, ['q2, 'p]: {x}
//     // In rustc Polonius, we have 'q1: 'r and 'q2: 'r

//     let mut y: i32 = 0;
//     let mut u: &'u1 mut i32 = &mut y; // 'u: {y}, 'r: {**q, p, x}, q1: {p}, ['q2, 'p]: {x}
//     let v: &'v1 mut &'v2 mut i32 = &mut u; // 'v1: {u}, ['v2, 'u]: {y}, 'r: {**q, p, x}, q1: {p}, ['q2, 'p]: {x}
//     if true {
//         // live regions: 'v1, 'v2, 'r
//         // Before this assignment, the loans environment is: 'v1: {u}, 'v2: {y}, 'r: {**q, p, x}
//         q = &mut *v; 
//         // In rustc Polonius, we have 'q2 = 'v2 so loans flow to 'v2 can flow to 'q2 and then can flow to 'r
//         // After this assignment, the loans environment is: 'v1: {u}, ['v2, 'q2]: {y}, 'r: {p, x}, 'q1: {*v, u}
//     };
//     // join of loans environment: 'v1: {u}, ['v2, 'q2]: {y, x}, 'r: {**q, p, x}, 'q1: {*v, p}
//     // live regions: 'q1, 'q2, 'r
//     // 'q2: {y, x}, 'r: {**q, p, x}, 'q1: {*v, p, u}
//     let tmp1: i32 = **q;
//     let tmp2: &mut i32 = &mut y; // y is an active loans because it is borrowed by 'q2

//     let tmp3: i32 = *r;
// }

// This example cannot pass rustc Polonius.
// rustc +nightly 50_region_relations_flow_sensitive.rs -Z polonius=next 
fn main() {
    let mut x: i32 = 0;
    let mut p: &mut i32 = &mut x; // 'p: {x}
    let mut q: &mut &mut i32 = &mut p; // 'q1: {p}, ['q2, 'p]: {x}
    let r: &i32 = &**q; // 'r: {**q, p, x}, q1: {p}, ['q2, 'p]: {x}

    let mut y: i32 = 0;
    let mut u: &mut i32 = &mut y; // 'u: {y}, 'r: {**q, p, x}, q1: {p}, ['q2, 'p]: {x}
    let v: &mut &mut i32 = &mut u; // 'v1: {u}, ['v2, 'u]: {y}, 'r: {**q, p, x}, q1: {p}, ['q2, 'p]: {x}

    if true {
        // live regions: 'v1, 'v2, 'r
        // Before this assignment, the loans environment is: 'v1: {u}, 'v2: {y}, 'r: {**q, p, x}
        q = &mut *v; 
        // After this assignment, the loans environment is: 'v1: {u}, ['v2, 'q2]: {y}, 'r: {p, x}, 'q1: {*v, u}
    };
    // join of loans environment: 'v1: {u}, ['v2, 'q2]: {y, x}, 'r: {**q, p, x}, 'q1: {*v, p}
    // live regions: 'q1, 'q2, 'r
    // 'q2: {y, x}, 'r: {**q, p, x}, 'q1: {*v, p, u}
    let tmp1: i32 = **q; // This is not an error because r is a shared reference and using **q is ok
    let tmp2: &mut i32 = &mut y; 

    let tmp3: i32 = *r;
}