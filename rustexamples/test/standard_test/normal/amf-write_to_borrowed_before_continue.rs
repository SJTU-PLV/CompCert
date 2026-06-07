// Source: borrowck.rs (write_to_borrowed_before_continue test)

fn main() {
    let mut a: i32 = 22;
    let p: &i32 = &a;
    loop {
        if true {
            a = 23; //~ ERROR cannot assign to `a` because it is borrowed
            continue;
        }
        break;
    }
    let _: i32 = *p;
}
