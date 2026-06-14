// Repo: rust-lang/rust
// Source: nll/self-assign-ref-mut.rs
// Check that `*y` isn't borrowed after `y = y`.

fn main() {
    let mut x: i32 = 1;
    {
        let mut y: &mut i32 = &mut x;
        y = y;
        let _u1: &mut i32 = y;
    }
    let _u2: i32 = x;
    {
        let mut y2: &mut i32 = &mut x;
        y2 = y2;
        y2 = y2;
        let _u3: &mut i32 = y2;
    }
    let _u4: i32 = x;
}
