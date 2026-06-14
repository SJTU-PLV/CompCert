// Source: nll/borrowed-universal-error-2.rs

struct ISingle { fst: i32 }

fn foo<'a>(x: &'a ISingle) -> &'a i32 {
    let v: i32 = 22;
    return &v; //~ ERROR E0515 cannot return reference to local variable
}

fn main() {
    let t: ISingle = ISingle { fst: 0 };
    let _u1: &i32 = foo(&t);
}
