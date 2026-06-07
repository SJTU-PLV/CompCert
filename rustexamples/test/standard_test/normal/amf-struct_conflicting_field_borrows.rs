// Source: borrowck.rs (struct_conflicting_field_borrows test)

struct Point { x: i32, y: i32 }

fn main() {
    let mut p: Point = Point { x: 0, y: 0 };
    let b1: &mut i32 = &mut p.x;
    p.x = 1; //~ ERROR cannot assign to `p.x` because it is borrowed
    let _: i32 = *b1;
}
