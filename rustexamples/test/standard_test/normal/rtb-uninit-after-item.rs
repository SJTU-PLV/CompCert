// Repo: rust-lang/rust
// Source: borrowck/borrowck-uninit-after-item.rs

fn baz(x: i32) {}

fn main() {
    let bar: i32;
    baz(bar); //~ ERROR E0381
}
