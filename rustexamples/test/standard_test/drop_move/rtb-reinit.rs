// Repo: rust-lang/rust
// Source: borrowck/borrowck-reinit.rs
// E0382: use of moved value after reinitialization and second move

struct IPairBox { fst: i32, snd: Box<i32> }

fn main() {
    let mut x: Box<i32> = Box::new(0);
    let _u: Box<i32> = x;
    x = Box::new(1);
    let _u1: Box<i32> = x;
    let _u2: IPairBox = IPairBox { fst: 1, snd: x }; //~ ERROR use of moved value: `x`
}
