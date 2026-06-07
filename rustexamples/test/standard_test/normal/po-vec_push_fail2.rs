// Source: inputs/vec-push-ref/vec-push-ref.rs (foo2 function)

enum MyOption<'a> { Some(&'a i32), None }

struct Holder<'a> { item: MyOption<'a> }

fn drop_holder<'a>(_: &mut Holder<'a>) {}

fn main() {
    let mut x: i32 = 22;
    let mut holder: Holder = Holder { item: MyOption::None };
    let p: &i32 = &x;

    if true {
        holder.item = MyOption::Some(p);
    } else {
        x = x + 1;
    }

    x = x + 1; //~ ERROR cannot assign to `x` because it is borrowed
    drop_holder(&mut holder);
}
