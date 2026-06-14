// Source: nll/issue-57989.rs
// Two errors: assign through & reference, AND assign because it is borrowed

fn f(x: &i32) {
    let g: & &i32 = &x;
    *x = 0; //~ ERROR E0594 cannot assign to `*x`, which is behind a `&` reference
    //~^ ERROR cannot assign to `*x` because it is borrowed
    let _u1: & &i32 = g;
}

fn main() {
    let v: i32 = 1;
    f(&v);
}
