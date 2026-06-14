// Source: nll/polonius/subset-relations.rs
// 'b: 'a is explicitly declared — returning y is OK

fn valid_subset<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32
where 'b: 'a {
    return y;
}

fn main() {
    let a: i32 = 1;
    let b: i32 = 2;
    let _u1: &i32 = valid_subset(&a, &b);
}
