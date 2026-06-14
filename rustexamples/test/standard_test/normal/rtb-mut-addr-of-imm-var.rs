// Repo: rust-lang/rust
// Source: borrowck/borrowck-mut-addr-of-imm-var.rs

fn main() {
    let x: i32 = 3;
    let y: &mut i32 = &mut x; //~ ERROR E0596 cannot borrow `x` as mutable, as it is not declared as mutable
    *y = 5;
    let _u1: i32 = *y;
}
