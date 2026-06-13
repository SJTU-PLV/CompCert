// Source: borrowck/borrowck-storage-dead.rs
// E0381: each loop iteration starts with a fresh uninitialized variable

fn ok() {
    loop {
        let _x: i32 = 1;
    }
}

fn fail() {
    loop {
        let x: i32;
        let _u1: i32 = x + 1; //~ ERROR E0381
    }
}

fn main() {
    ok();
    fail();
}
