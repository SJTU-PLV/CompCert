// Repo: rust-lang/rust
// Source: nll/borrowed-temporary-error.rs
// Temporary tuple value dropped while borrowed

struct IPair { fst: i32 }

fn gimme(x: &IPair) -> &i32 {
    return &x.fst;
}

fn main() {
    let v: i32 = 22;
    let x: &i32 = gimme(&IPair { fst: v });
    //~^ ERROR E0716 temporary value dropped while borrowed
    let _u1: i32 = *x;
}
