// Repo: rust-lang/rust
// Source: nll/polonius/subset-relations.rs
// 'b: 'a is not known — returning y requires it

fn missing_subset<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 {
    return y; //~ ERROR lifetime may not live long enough
}

fn main() {
    let a: i32 = 1;
    let b: i32 = 2;
    let _u1: &i32 = missing_subset(&a, &b);
}
