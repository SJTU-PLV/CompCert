// Repo: rust-lang/rust
// Source: nll/issue-46036.rs
// Issue 46036: [NLL] false edges on infinite loops
// Infinite loops should create false edges to the cleanup block.

struct Foo { x: &'static i32 }

fn foo() {
    let a: i32 = 3;
    let foo: Foo = Foo { x: &a }; //~ ERROR E0597
    loop { }
}

fn main() {
    foo();
}
