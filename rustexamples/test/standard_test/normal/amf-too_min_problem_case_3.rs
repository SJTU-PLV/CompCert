// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (too_min_problem_case_3 test)

struct Map { value: i32 }

fn min_problem_case_3<'a>(m: &'a mut Map) -> &'a mut Map {
    let n: &mut Map = &mut *m;
    if true {
    } else {
    }
    // n is dead here, so reborrow is allowed
    let o: &mut Map = &mut *m;
    return o;
}

fn main() {
    let mut m: Map = Map { value: 1 };
    let _: &mut Map = min_problem_case_3(&mut m);
}
