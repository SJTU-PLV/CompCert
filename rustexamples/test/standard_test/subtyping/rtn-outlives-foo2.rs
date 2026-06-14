// Repo: rust-lang/rust
// Source: nll/outlives-suggestion-simple.rs
// 'a may not be 'static

fn foo2<'a>(x: &'a i32) -> &'static i32 {
    return x; //~ ERROR lifetime may not live long enough
}

fn main() {
    let val: i32 = 42;
    let _u1: &i32 = foo2(&val);
}
