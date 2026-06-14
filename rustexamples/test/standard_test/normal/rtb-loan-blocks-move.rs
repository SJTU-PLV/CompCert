// Repo: rust-lang/rust
// Source: borrowck/borrowck-loan-blocks-move.rs

fn take(_v: Box<i32>) {
}



fn box_imm() {
    let v: Box<i32> = Box::new(3);
    let w: &Box<i32> = &v;
    take(v); //~ ERROR cannot move out of `v` because it is borrowed
    let _u1: &Box<i32> = w;
}

fn main() {
    box_imm();
}
