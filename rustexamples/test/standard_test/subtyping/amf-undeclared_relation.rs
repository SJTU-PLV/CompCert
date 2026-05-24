// Source: borrowck.rs (undeclared_universal_region_relationship test)

fn foo<'a, 'b>(v1: &'a i32) -> &'b i32 {
    return v1
}

fn main() {
    let val: i32 = 42;
    let _: &i32 = foo(&val);
}
