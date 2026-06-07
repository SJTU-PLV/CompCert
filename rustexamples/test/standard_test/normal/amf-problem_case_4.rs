// Source: borrowck.rs (problem_case_4 test)

struct Map { value: i32 }

fn min_problem_case_4<'a>(mut list: &'a mut Map, list2: &'a mut Map) -> i32 {
    let num: &mut i32 = &mut (*list).value;
    list = &mut *list2; // reassign list to point to list2
    let _: &mut i32 = num; // num still valid — it borrows the original pointee
    return 0;
}

fn main() {
    let mut m1: Map = Map { value: 1 };
    let mut m2: Map = Map { value: 2 };
    let _: i32 = min_problem_case_4(&mut m1, &mut m2);
}
