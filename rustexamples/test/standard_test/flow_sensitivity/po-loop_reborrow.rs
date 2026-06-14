// Repo: rust-lang/polonius
// Source: inputs/issue-47680/issue-47680.rs

enum MyOption<'a> { Some(&'a mut i32), None }

fn maybe_next<'a>(x: &'a mut i32, ret: &mut MyOption<'a>) {
    *ret = MyOption::None;
}

fn main() {
    let mut val: i32 = 42;
    let mut temp: &mut i32 = &mut val;
    loop {
        let mut opt: MyOption = MyOption::None;
        maybe_next(&mut *temp, &mut opt);
        match opt {
            MyOption::Some(v) => { temp = v; }
            MyOption::None => { }
        }
    }
}
