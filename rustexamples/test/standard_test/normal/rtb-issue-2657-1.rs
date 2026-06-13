// Source: borrowck/borrowck-issue-2657-1.rs

enum MyOption {
    Some(Box<i32>),
    None
}

fn main() {
    let x: MyOption = MyOption::Some(Box::new(1));
    match x {
        MyOption::Some(ref y) => {
            let _a: MyOption = x; //~ ERROR cannot move
            let _u1: &Box<i32> = y;
        }
        _ => {}
    };
}
