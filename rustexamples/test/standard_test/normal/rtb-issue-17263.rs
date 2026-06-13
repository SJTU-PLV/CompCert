// Source: borrowck/issue-17263.rs

struct Foo { a: i32, b: i32 }

fn main() {
    let mut x: Box<Foo> = Box::new(Foo { a: 1, b: 2 });
    let a: &mut i32 = &mut (*x).a;
    let b: &mut i32 = &mut (*x).b;

    let mut foo: Box<Foo> = Box::new(Foo { a: 1, b: 2 });
    let c: &mut i32 = &mut (*foo).a;
    let d: &i32 = &(*foo).b;

    // We explicitly use the references created above to illustrate that the
    // borrow checker is accepting this code *not* because of artificially
    // short lifetimes, but rather because it understands that all the
    // references are of disjoint parts of memory.
    let _u1: &i32 = d;
    let _u2: &mut i32 = c;
    let _u3: &mut i32 = b;
    let _u4: &mut i32 = a;
}
