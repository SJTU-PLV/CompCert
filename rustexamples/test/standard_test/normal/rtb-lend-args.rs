// Repo: rust-lang/rust
// Source: borrowck/borrowck-lend-args.rs
// Positive test: borrowing through Box from function arguments

fn borrow(_v: &i32) {}

fn borrow_from_arg_imm_ref(v: Box<i32>) {
    borrow(&*v);
}

fn borrow_from_arg_mut_ref(v: &mut Box<i32>) {
    borrow(&**v);
}

fn borrow_from_arg_copy(v: Box<i32>) {
    borrow(&*v);
}

fn main() {
    borrow_from_arg_imm_ref(Box::new(1));
    borrow_from_arg_mut_ref(&mut Box::new(2));
    borrow_from_arg_copy(Box::new(3));
}
