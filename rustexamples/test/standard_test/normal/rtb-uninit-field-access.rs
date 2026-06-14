// Repo: rust-lang/rust
// Source: borrowck/borrowck-uninit-field-access.rs
// Check that we do not allow access to fields of uninitialized or moved structs.

struct Point {
    x: i32,
    y: i32
}

fn main() {
    let mut a: Point;
    let _u1: i32 = a.x + 1; //~ ERROR [E0381]
}
