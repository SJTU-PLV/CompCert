// Source: borrowck.rs (undeclared_transitive_universal_region_relationship test)

fn foo<'a, 'b, 'c>(v1: &'a i32) -> &'c i32
where 'a: 'b
{
    return v1
}

fn main() {
    let val: i32 = 42;
    let _: &i32 = foo(&val);
}
