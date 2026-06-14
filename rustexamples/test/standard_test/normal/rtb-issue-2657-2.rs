// Repo: rust-lang/rust
// Source: borrowck/borrowck-issue-2657-2.rs

enum MyOption {
    Some(Box<i32>),
    None
}

fn main() {
    let x: MyOption = MyOption::Some(Box::new(1));

    match x {
        MyOption::Some(ref y) => {
            let _b: Box<i32> = *y; //~ ERROR cannot move out
        }
        _ => {}
    };
}
