// Repo: rust-lang/rust
// Source: borrowck/return-ref-to-temporary.rs
// E0515: cannot return reference to temporary value

fn bar<'a>() -> &'a mut i32 {
    return &mut 4; //~ ERROR E0515
}

fn main() {}
