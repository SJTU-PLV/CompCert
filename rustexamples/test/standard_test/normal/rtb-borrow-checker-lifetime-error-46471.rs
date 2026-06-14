// Repo: rust-lang/rust
// Source: borrowck/borrow-checker-lifetime-error-46471.rs
// E0597: `z` does not live long enough — reference outlives inner block

fn main() {
    let y: &mut i32;
    {
        let mut z: i32 = 0;
        y = &mut z;
    } // z dropped here
    let _u1: &mut i32 = y; //~ ERROR `z` does not live long enough [E0597]
}
