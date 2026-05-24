// Source: inputs/subset-relations/subset-relations.rs (missing_subset function)

fn missing_subset<'a, 'b>(_x: &'a i32, y: &'b i32) -> &'a i32 {
    return y
}

fn main() {
    let a: i32 = 1;
    let b: i32 = 2;
    let _: &i32 = missing_subset(&a, &b);
}
