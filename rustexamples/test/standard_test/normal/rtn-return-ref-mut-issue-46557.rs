// Source: nll/return-ref-mut-issue-46557.rs
// Cannot return value referencing temporary value

fn gimme_static_mut() -> &'static mut i32 {
    let mut x: i32 = 1234543;
    let r: &mut i32 = &mut x;
    return r; //~ ERROR E0515 cannot return value referencing local variable
}

fn main() {
    let _u1: &mut i32 = gimme_static_mut();
}
