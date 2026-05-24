// Source: inputs/vec-push-ref/vec-push-ref.rs (foo3 function, rewritten with MyOption and Holder)

enum MyOption<'a> { Some(&'a i32), None }

struct Holder<'a> { item: MyOption<'a> }

fn drop<'a>(_: &mut Holder<'a>) {}

fn main() {
    let mut x: i32 = 22;
    let mut holder: Holder = Holder { item: MyOption::None };
    let p: &i32 = &x;

    if true {
        holder.item = MyOption::Some(p);
    } else {
        x = x + 1;
    }

    drop(&mut holder);
}
