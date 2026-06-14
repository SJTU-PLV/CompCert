// Source: nll/polonius/subset-relations.rs
// &'a &'b mut i32 implies 'b: 'a, so returning x is OK

fn implied_bounds_subset<'a, 'b>(x: &'a &'b mut i32) -> &'a i32 {
    return &**x;
}

fn main() {
    let mut val: i32 = 42;
    let r: &mut i32 = &mut val;
    let p: & &mut i32 = &r;
    let _u1: &i32 = implied_bounds_subset(p);
}
