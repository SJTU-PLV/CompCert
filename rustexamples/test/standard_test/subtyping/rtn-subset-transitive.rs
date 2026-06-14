// Source: nll/polonius/subset-relations.rs
// 'b: 'a declared + 'a: 'c implied → 'b: 'c transitive, returning y is OK

fn transitively_valid_subset<'a, 'b, 'c>(x: &'c &'a i32, y: &'b i32) -> &'c i32
where 'b: 'a {
    return y;
}

fn main() {
    let val1: i32 = 1;
    let val2: i32 = 2;
    let p: &i32 = &val1;
    let _u1: &i32 = transitively_valid_subset(&p, &val2);
}
