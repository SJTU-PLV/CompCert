// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (loan_cannot_outlive_lifetime_fail test)

fn main() {
    let mut x: i32 = 22;
    let p: &i32 = &x;
    let q: &i32 = p;
    x = 1; //~ ERROR cannot assign to `x` because it is borrowed
    let _: &i32 = q;
}
