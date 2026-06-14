// Repo: rust-lang/rust
// Source: borrowck/reassignment_immutable_fields_twice.rs
// This should never be allowed -- since `x` is not `mut`, so `x.fst` cannot be assigned twice.

struct IPair { fst: i32, snd: i32 }

fn var_then_field() {
    let x: IPair;
    x = IPair { fst: 22, snd: 44 };
    x.fst = 1; //~ ERROR
}

fn same_field_twice() {
    let x: IPair;
    x.fst = 1; //~ ERROR
    x.fst = 22;
    x.snd = 44;
}

fn main() {
    var_then_field();
    same_field_twice();
}
