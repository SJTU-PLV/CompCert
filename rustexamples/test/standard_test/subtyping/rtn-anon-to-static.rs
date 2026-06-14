// Source: nll/nll-anon-to-static.rs
// Cannot reborrow and return as 'static when input lifetime is shorter

fn foo<'a>(x: &'a i32) -> &'static i32 {
    return &*x; //~ ERROR lifetime may not live long enough
}

fn main() {
    let val: i32 = 42;
    let _u1: &i32 = foo(&val);
}
