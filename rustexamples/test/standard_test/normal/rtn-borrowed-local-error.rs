// Repo: rust-lang/rust
// Source: nll/borrowed-local-error.rs

struct ISingle { fst: i32 }

fn gimme(x: &ISingle) -> &i32 {
    return &x.fst;
}

fn main() {
    let x: &i32;
    {
        let v: ISingle = ISingle { fst: 22 };
        x = gimme(&v);
        //~^ ERROR `v` does not live long enough [E0597]
    }
    let _u1: &i32 = x;
}
