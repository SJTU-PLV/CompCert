// Repo: rust-lang/rust
// Source: nll/reference-carried-through-struct-field.rs
// E0503: cannot use `x` because it was mutably borrowed through struct field

struct Wrap<'a> { w: &'a mut i32 }

fn foo() {
    let mut x: i32 = 22;
    let wrapper: Wrap = Wrap { w: &mut x };
    x = x + 1; //~ ERROR cannot use `x` because it was mutably borrowed [E0503]
    *wrapper.w = *wrapper.w + 1;
}

fn main() {
    foo();
}
