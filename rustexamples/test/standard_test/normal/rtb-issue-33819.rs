// Source: borrowck/issue-33819.rs
// E0596: cannot borrow `ref` binding as mutable (immutable pattern binding)

enum MyOption {
    Some(i32),
    None
}

fn main() {
    let mut op: MyOption = MyOption::Some(2);
    match op {
        MyOption::Some(ref v) => {
            let a: &mut &i32 = &mut v; //~ ERROR cannot borrow `v` as mutable
            let _u1: &mut &i32 = a;
        }
        MyOption::None => {}
    };
}
