// Source: borrowck.rs (min_problem_case_3 test)

struct Map { v: i32 }

fn min_problem_case_3(m: &mut Map) -> &mut Map {
    let n: &mut Map = &mut *m;
    if true {
        return n;
    } else {
        let o: &mut Map = &mut *m;
        return o;
    }
}

fn main() {
    let mut m: Map = Map { v: 42 };
    let _: &mut Map = min_problem_case_3(&mut m);
}