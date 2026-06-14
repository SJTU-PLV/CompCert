// Repo: rust-lang/rust
// Source: borrowck/borrowck-borrowed-uniq-rvalue.rs

fn store_ref<'a>(dst: &mut &'a i32, src: &'a i32) {
    *dst = src;
}

fn main() {
    let tmp: Box<i32>;
    let mut r: &i32 = &0;

    store_ref(&mut r, &*Box::new(1)); //~ ERROR temporary value dropped while borrowed
    let _u1: &i32 = r;

    // but it is ok if we use a named variable
    tmp = Box::new(2);
    store_ref(&mut r, &*tmp);
    let _u2: &i32 = r;
}
