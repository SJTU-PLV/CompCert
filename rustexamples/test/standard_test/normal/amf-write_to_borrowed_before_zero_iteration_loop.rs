// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (write_to_borrowed_before_zero_iteration_loop test)

fn main() {
    let mut a: i32 = 22;
    let b: i32 = 22;
    let p: &i32 = &a;
    a = 23; //~ ERROR cannot assign to `a` because it is borrowed
    loop {
        let _u1: &i32 = &b;
        break;
    }
    let _u2: i32 = *p;
}
