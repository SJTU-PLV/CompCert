// Source: borrowck.rs (move_parent_then_access_child test)

struct Inner { bar: i32 }

struct Outer { foo: Inner }

fn main() {
    let x: Outer = Outer { foo: Inner { bar: 1 } };
    let _a: Inner = x.foo;
    let _b: i32 = x.foo.bar; //~ ERROR use of moved value: `x.foo`
}
