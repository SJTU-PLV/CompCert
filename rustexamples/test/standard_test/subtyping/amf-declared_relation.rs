// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (declared_universal_region_relationship test)

fn foo<'a, 'b>(v1: &'a i32) -> &'b i32
where 'a: 'b
{
    return v1
}

fn main() {
    let val: i32 = 42;
    let _: &i32 = foo(&val);
}
