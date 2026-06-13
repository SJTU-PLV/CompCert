// Source: borrowck/borrowck-anon-fields-struct.rs
// Disjoint borrows of struct fields: different fields OK, same field errors

struct Y { x: i32, y: i32 }

fn distinct_variant() {
    let mut y: Y = Y { x: 1, y: 2 };
    let a: &mut i32 = &mut y.x;
    let b: &mut i32 = &mut y.y;
    *a = *a + 1;
    *b = *b + 1;
}

fn same_variant() {
    let mut y: Y = Y { x: 1, y: 2 };
    let a: &mut i32 = &mut y.x;
    let b: &mut i32 = &mut y.x; //~ ERROR cannot borrow `y.x` as mutable more than once
    *a = *a + 1;
    *b = *b + 1;
}

fn main() {
    distinct_variant();
    same_variant();
}
