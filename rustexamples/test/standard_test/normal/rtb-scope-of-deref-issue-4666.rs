// Repo: rust-lang/rust
// Source: borrowck/borrowck-scope-of-deref-issue-4666.rs
// Tests that the scope of the pointer returned from `get()` is
// limited to the deref operation itself, and does not infect the
// block as a whole.

struct MyBox {
    x: i32
}

fn get(b: &MyBox) -> &i32 {
    return &b.x;
}

fn set(b: &mut MyBox, x: i32) {
    b.x = x;
}

fn fun1() {
    // in the past, borrow checker behaved differently when
    // init and decl of `v` were distinct
    let v: i32;
    let mut a_box: MyBox = MyBox { x: 0 };
    set(&mut a_box, 22);
    v = *get(&a_box);
    set(&mut a_box, v + 1);
    let _u1: i32 = *get(&a_box);
}

fn fun2() {
    let mut a_box: MyBox = MyBox { x: 0 };
    set(&mut a_box, 22);
    let v: i32 = *get(&a_box);
    set(&mut a_box, v + 1);
    let _u1: i32 = *get(&a_box);
}

fn main() {
    fun1();
    fun2();
}
