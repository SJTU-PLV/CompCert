// Repo: rust-lang/rust
// Source: nll/outlives-suggestion-simple.rs
// 'a: 'b is not known to hold

fn foo1<'a, 'b>(x: &'a i32) -> &'b i32 {
    return x; //~ ERROR lifetime may not live long enough
}

fn main() {
    let val: i32 = 42;
    let _u1: &i32 = foo1(&val);
}
