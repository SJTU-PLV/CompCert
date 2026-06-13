// Source: borrowck/borrowck-reborrow-from-mut.rs
// Removed: borrow_both_mut_pattern, borrow_var_and_pattern (struct patterns not supported).

struct Foo {
    bar1: Bar,
    bar2: Bar
}

struct Bar {
    int1: i32,
    int2: i32
}

fn borrow_same_field_twice_mut_mut(foo: &mut Foo) {
    let _bar1: &mut Bar = &mut foo.bar1;
    let _bar2: &mut Bar = &mut foo.bar1; //~ ERROR cannot borrow
    let _u1: &mut Bar = _bar1;
}

fn borrow_same_field_twice_mut_imm(foo: &mut Foo) {
    let _bar1: &mut Bar = &mut foo.bar1;
    let _bar2: &Bar = &foo.bar1; //~ ERROR cannot borrow
    let _u1: &mut Bar = _bar1;
}

fn borrow_same_field_twice_imm_mut(foo: &mut Foo) {
    let _bar1: &Bar = &foo.bar1;
    let _bar2: &mut Bar = &mut foo.bar1; //~ ERROR cannot borrow
    let _u1: &Bar = _bar1;
}

fn borrow_same_field_twice_imm_imm(foo: &mut Foo) {
    let _bar1: &Bar = &foo.bar1;
    let _bar2: &Bar = &foo.bar1;
    let _u1: &Bar = _bar1;
}

fn borrow_both_mut(foo: &mut Foo) {
    let _bar1: &mut Bar = &mut foo.bar1;
    let _bar2: &mut Bar = &mut foo.bar2;
    let _u1: &mut Bar = _bar1;
}

fn borrow_mut_and_base_imm(foo: &mut Foo) {
    let _bar1: &mut i32 = &mut foo.bar1.int1;
    let _foo1: &Bar = &foo.bar1; //~ ERROR cannot borrow
    let _foo2: &Foo = &*foo; //~ ERROR cannot borrow
    let _u1: &mut i32 = _bar1;
}

fn borrow_mut_and_base_mut(foo: &mut Foo) {
    let _bar1: &mut i32 = &mut foo.bar1.int1;
    let _foo1: &mut Bar = &mut foo.bar1; //~ ERROR cannot borrow
    let _u1: &mut i32 = _bar1;
}

fn borrow_mut_and_base_mut2(foo: &mut Foo) {
    let _bar1: &mut i32 = &mut foo.bar1.int1;
    let _foo2: &mut Foo = &mut *foo; //~ ERROR cannot borrow
    let _u1: &mut i32 = _bar1;
}

fn borrow_imm_and_base_mut(foo: &mut Foo) {
    let _bar1: &i32 = &foo.bar1.int1;
    let _foo1: &mut Bar = &mut foo.bar1; //~ ERROR cannot borrow
    let _u1: &i32 = _bar1;
}

fn borrow_imm_and_base_mut2(foo: &mut Foo) {
    let _bar1: &i32 = &foo.bar1.int1;
    let _foo2: &mut Foo = &mut *foo; //~ ERROR cannot borrow
    let _u1: &i32 = _bar1;
}

fn borrow_imm_and_base_imm(foo: &mut Foo) {
    let _bar1: &i32 = &foo.bar1.int1;
    let _foo1: &Bar = &foo.bar1;
    let _foo2: &Foo = &*foo;
    let _u1: &i32 = _bar1;
}

fn borrow_mut_and_imm(foo: &mut Foo) {
    let _bar1: &mut Bar = &mut foo.bar1;
    let _foo1: &Bar = &foo.bar2;
    let _u1: &mut Bar = _bar1;
}

fn borrow_mut_from_imm(foo: &Foo) {
    let _bar1: &mut Bar = &mut foo.bar1; //~ ERROR cannot borrow
}

fn borrow_long_path_both_mut(foo: &mut Foo) {
    let _bar1: &mut i32 = &mut foo.bar1.int1;
    let _foo1: &mut i32 = &mut foo.bar2.int2;
    let _u1: &mut i32 = _bar1;
}

fn main() {
    let mut foo: Foo = Foo {
        bar1: Bar { int1: 1, int2: 2 },
        bar2: Bar { int1: 3, int2: 4 }
    };
    borrow_same_field_twice_mut_mut(&mut foo);
    borrow_same_field_twice_mut_imm(&mut foo);
    borrow_same_field_twice_imm_mut(&mut foo);
    borrow_same_field_twice_imm_imm(&mut foo);
    borrow_both_mut(&mut foo);
    borrow_mut_and_base_imm(&mut foo);
    borrow_mut_and_base_mut(&mut foo);
    borrow_mut_and_base_mut2(&mut foo);
    borrow_imm_and_base_mut(&mut foo);
    borrow_imm_and_base_mut2(&mut foo);
    borrow_imm_and_base_imm(&mut foo);
    borrow_mut_and_imm(&mut foo);
    borrow_mut_from_imm(&foo);
    borrow_long_path_both_mut(&mut foo);
}
