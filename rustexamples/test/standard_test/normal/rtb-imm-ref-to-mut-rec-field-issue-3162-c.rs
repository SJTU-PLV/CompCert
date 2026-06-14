// Repo: rust-lang/rust
// Source: borrowck/borrowck-imm-ref-to-mut-rec-field-issue-3162-c.rs
// Reborrow of &mut through &*b blocks mutation of original variable

fn main() {
    let mut a: i32 = 3;
    let b: &mut i32 = &mut a;
    {
        let c: &i32 = &*b;
        a = 4; //~ ERROR cannot assign to `a` because it is borrowed
        let _u1: &i32 = c;
    }
    let _u2: &mut i32 = b;
}
