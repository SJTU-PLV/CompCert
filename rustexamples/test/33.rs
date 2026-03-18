fn main(){
    let mut v1: i32 = 22;
    let mut v2: i32 = 44;
    let mut p2: &mut i32 = &mut v2; // 'p2 -> {v2}
    let mut p1: &mut i32 = &mut v1; // 'p1 -> {v1}, 'p2 -> {v2}
    let mut q: &mut &mut i32;
    if true {
        q = &mut p1;
    } else{
        q = &mut p2;
    } // 'q1 -> {p1, p2}, ['p1, 'p2, 'q2] -> {v1, v2}
    **q = 3; // The following three lines are used to make sure that ‘q1, 'q2, 'p1 and 'p2 are all live before the end of the if-then-else, so that their invariant relations are merged at line 11
    *p2 = 3;
    *p1 = 2; // note that if we comment line 12, there is no error reported, because the relations betweem ('p1, 'q2) and ('p2, 'q2) are not merged
    v1 = 13; // Using v1 should not invalidate p2 as it is impossible that p2 points to v1
             // 'q1 -> {p1, p2}, ['p1, 'p2, 'q2] -> Invalid
    // *p2 = 3; // If we uncomment this line, error should be reported at line 15 (the last line)
}