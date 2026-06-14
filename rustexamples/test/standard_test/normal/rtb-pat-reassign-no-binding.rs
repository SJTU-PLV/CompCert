// Repo: rust-lang/rust
// Source: borrowck/borrowck-pat-reassign-no-binding.rs
// Positive test: reassign in match arm where no borrow exists is OK

enum MyOption {
    Some(i32),
    None
}

fn main() {
    let mut x: MyOption = MyOption::None;
    match x {
        MyOption::None => {
            // OK: no outstanding loan, reassign is allowed
            x = MyOption::Some(0);
        }
        MyOption::Some(_) => {}
    };
    let _u1: MyOption = x;
}
