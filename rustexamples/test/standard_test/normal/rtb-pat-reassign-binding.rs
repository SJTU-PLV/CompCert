// Source: borrowck/borrowck-pat-reassign-binding.rs
// E0506: match arm with ref borrow prevents reassignment of matched variable

enum MyOption {
    Some(i32),
    None
}

fn main() {
    let mut x: MyOption = MyOption::None;
    match x {
        MyOption::None => {
            x = MyOption::Some(0);
        }
        MyOption::Some(ref i) => {
            x = MyOption::Some(*i + 1); //~ ERROR cannot assign to `x` because it is borrowed
            let _u1: &i32 = i;
        }
    };
    let _u2: MyOption = x;
}
