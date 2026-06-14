// Repo: rust-lang/rust
// Source: borrowck/borrowck-lend-flow.rs
// Note: the borrowck analysis is currently flow-insensitive.
// Therefore, some of these errors are marked as spurious and could be
// corrected by a simple change to the analysis.  The others are
// either genuine or would require more advanced changes.  The latter
// cases are noted.



fn borrow(_v: &i32) {}
fn borrow_mut(_v: &mut i32) {}
fn cond() -> bool { return false; }

fn inc(v: &mut Box<i32>) {
    *v = Box::new(**v + 1);
}

fn pre_freeze() {
    // In this instance, the freeze starts before the mut borrow.

    let mut v: Box<i32> = Box::new(3);
    let w: &Box<i32> = &v;
    borrow_mut(&mut *v); //~ ERROR cannot borrow
    let _u1: &Box<i32> = w;
}

fn post_freeze() {
    // In this instance, the const alias starts after the borrow.

    let mut v: Box<i32> = Box::new(3);
    borrow_mut(&mut *v);
    let _w: &Box<i32> = &v;
}

fn main() {
    pre_freeze();
    post_freeze();
}
