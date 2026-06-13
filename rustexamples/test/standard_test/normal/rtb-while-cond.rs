// Source: borrowck/borrowck-while-cond.rs

fn main() {
    let x: bool;
    while (x) {} //~ ERROR E0381
}
