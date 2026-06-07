// Source: inputs/maybe-initialized-drop/maybe-initialized-drop.rs

struct Wrap<'p> { p: &'p mut i32 }

fn drop_wrap<'p>(_: Wrap<'p>) {}

fn main() {
    let mut x: i32 = 0;
    let wrap: Wrap = Wrap { p: &mut x };
    x = 1; //~ ERROR cannot assign to `x` because it is borrowed
    drop_wrap(wrap);
}
