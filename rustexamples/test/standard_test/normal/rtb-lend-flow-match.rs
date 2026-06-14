// Repo: rust-lang/rust
// Source: borrowck/borrowck-lend-flow-match.rs
// E0506: match arm with ref borrow blocks reassignment; arm without borrow allows it

enum MyOption {
    Some(i32),
    None
}

fn separate_arms() {
    let mut x: MyOption = MyOption::None;
    match x {
        MyOption::None => {
            // OK: no outstanding loan, reassign is allowed
            x = MyOption::Some(0);
        }
        MyOption::Some(ref r) => {
            x = MyOption::Some(1); //~ ERROR cannot assign to `x` because it is borrowed
            let _u1: &i32 = r;
        }
    };
}

fn main() {
    separate_arms();
}
