// Source: borrowck.rs (undeclared_universal_region_relationship_no_return test)

fn foo<'a, 'b>(x: &'a i32, y: &'b i32) {
    let mut output: &'b i32 = y;
    loop {
        output = x; //~ ERROR lifetime may not live long enough
    }
}

fn main() {
    let a: i32 = 1;
    let b: i32 = 2;
    foo(&a, &b);
}
