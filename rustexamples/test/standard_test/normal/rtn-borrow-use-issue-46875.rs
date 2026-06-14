// Source: nll/borrow-use-issue-46875.rs
// Borrow that ends before mutation is OK

fn main() {
    let mut x: i32 = 5;
    let y: &i32 = &x;
    let _u1: i32 = *y; // last use of y — borrow ends here
    x = 7; // OK, borrow has ended
    let _u2: i32 = x;
}
