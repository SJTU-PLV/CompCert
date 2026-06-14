// Repo: rust-lang/rust
// Source: borrowck/borrowck-borrow-from-owned-ptr.rs
// Field-level borrow tests through Box<Foo>: same field twice, different fields,
// subpath vs ancestor path conflicts with Box indirection.
// Removed: make_foo() (replaced with inline Box construction),
// match-based functions (struct patterns not supported).

struct Foo {
    bar1: Bar,
    bar2: Bar
}

struct Bar {
    int1: i32,
    int2: i32
}

fn borrow_same_field_twice_mut_mut() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut Bar = &mut (*foo).bar1;
    let _bar2: &mut Bar = &mut (*foo).bar1; //~ ERROR cannot borrow
    let _u1: &mut Bar = bar1;
}

fn borrow_same_field_twice_mut_imm() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut Bar = &mut (*foo).bar1;
    let _bar2: &Bar = &(*foo).bar1; //~ ERROR cannot borrow
    let _u1: &mut Bar = bar1;
}

fn borrow_same_field_twice_imm_mut() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &Bar = &(*foo).bar1;
    let _bar2: &mut Bar = &mut (*foo).bar1; //~ ERROR cannot borrow
    let _u1: &Bar = bar1;
}

fn borrow_same_field_twice_imm_imm() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &Bar = &(*foo).bar1;
    let _bar2: &Bar = &(*foo).bar1;
    let _u1: &Bar = bar1;
}

fn borrow_both_fields_mut() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut Bar = &mut (*foo).bar1;
    let _bar2: &mut Bar = &mut (*foo).bar2;
    let _u1: &mut Bar = bar1;
}

fn borrow_mut_and_base_imm() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut i32 = &mut (*foo).bar1.int1;
    let _foo1: &Bar = &(*foo).bar1; //~ ERROR cannot borrow
    let _foo2: &Foo = &*foo; //~ ERROR cannot borrow
    let _u1: i32 = *bar1;
}

fn borrow_mut_and_base_mut() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut i32 = &mut (*foo).bar1.int1;
    let _foo1: &mut Bar = &mut (*foo).bar1; //~ ERROR cannot borrow
    let _u1: i32 = *bar1;
}

fn borrow_mut_and_base_mut2() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut i32 = &mut (*foo).bar1.int1;
    let _foo2: &mut Foo = &mut *foo; //~ ERROR cannot borrow
    let _u1: i32 = *bar1;
}

fn borrow_imm_and_base_mut() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &i32 = &(*foo).bar1.int1;
    let _foo1: &mut Bar = &mut (*foo).bar1; //~ ERROR cannot borrow
    let _u1: i32 = *bar1;
}

fn borrow_imm_and_base_mut2() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &i32 = &(*foo).bar1.int1;
    let _foo2: &mut Foo = &mut *foo; //~ ERROR cannot borrow
    let _u1: i32 = *bar1;
}

fn borrow_imm_and_base_imm() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &i32 = &(*foo).bar1.int1;
    let _foo1: &Bar = &(*foo).bar1;
    let _foo2: &Foo = &*foo;
    let _u1: i32 = *bar1;
}

fn borrow_mut_and_imm() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut Bar = &mut (*foo).bar1;
    let _foo1: &Bar = &(*foo).bar2;
    let _u1: &mut Bar = bar1;
}

fn borrow_mut_from_imm() {
    let foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut Bar = &mut (*foo).bar1; //~ ERROR cannot borrow
    let _u1: &mut Bar = bar1;
}

fn borrow_long_path_both_mut() {
    let mut foo: Box<Foo> = Box::new(Foo { bar1: Bar { int1: 1, int2: 2 }, bar2: Bar { int1: 3, int2: 4 } });
    let bar1: &mut i32 = &mut (*foo).bar1.int1;
    let foo1: &mut i32 = &mut (*foo).bar2.int2;
    let _u1: i32 = *bar1;
    let _u2: i32 = *foo1;
}

fn main() {
    borrow_same_field_twice_mut_mut();
    borrow_same_field_twice_mut_imm();
    borrow_same_field_twice_imm_mut();
    borrow_same_field_twice_imm_imm();
    borrow_both_fields_mut();
    borrow_mut_and_base_imm();
    borrow_mut_and_base_mut();
    borrow_mut_and_base_mut2();
    borrow_imm_and_base_mut();
    borrow_imm_and_base_mut2();
    borrow_imm_and_base_imm();
    borrow_mut_and_imm();
    borrow_mut_from_imm();
    borrow_long_path_both_mut();
}
