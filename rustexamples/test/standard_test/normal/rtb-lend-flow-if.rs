// Source: borrowck/borrowck-lend-flow-if.rs
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

fn pre_freeze_cond() {
    // In this instance, the freeze is conditional and starts before
    // the mut borrow.

    let u: Box<i32> = Box::new(0);
    let mut v: Box<i32> = Box::new(3);
    let mut w: &Box<i32> = &u;
    if cond() {
        w = &v;
    }
    borrow_mut(&mut *v); //~ ERROR cannot borrow
    let _u1: &Box<i32> = w;
}

fn pre_freeze_else() {
    // In this instance, the freeze and mut borrow are on separate sides
    // of the if.

    let u: Box<i32> = Box::new(0);
    let mut v: Box<i32> = Box::new(3);
    let mut w: &Box<i32> = &u;
    if cond() {
        w = &v;
    } else {
        borrow_mut(&mut *v);
    }
    let _u1: &Box<i32> = w;
}

fn main() {
    pre_freeze_cond();
    pre_freeze_else();
}
