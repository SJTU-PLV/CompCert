// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (struct_disjoint_field_borrows test)

struct Point { x: i32, y: i32 }

fn main() {
    let mut p: Point = Point { x: 0, y: 0 };
    let b1: &mut i32 = &mut p.x;
    let b2: &mut i32 = &mut p.y;
    *b1 = 1;
    *b2 = 2;
}
