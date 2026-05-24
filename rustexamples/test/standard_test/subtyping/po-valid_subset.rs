// Source: inputs/subset-relations/subset-relations.rs (valid_subset function)

fn valid_subset<'a, 'b>(_x: &'a i32, y: &'b i32) -> &'a i32
where 'b: 'a
{
    return y
}

fn main() {
    let a: i32 = 1;
    let b: i32 = 2;
    let _: &i32 = valid_subset(&a, &b);
}
