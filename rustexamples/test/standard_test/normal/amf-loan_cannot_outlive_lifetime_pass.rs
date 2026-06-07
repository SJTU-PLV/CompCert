// Source: borrowck.rs (loan_cannot_outlive_lifetime_pass test)

fn main() {
    let mut x: i32 = 22;
    let p: &i32 = &x;
    let q: &i32 = p;
    x = x + 1; // OK, borrow dies before mutation
    let _: i32 = x;
}
