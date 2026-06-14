// Repo: rust-lang/rust
// Source: nll/borrowed-match-issue-45045.rs
// Regression test for issue #45045

enum Xyz {
    A,
    B
}

fn main() {
    let mut e: Xyz = Xyz::A;
    let f: &mut Xyz = &mut e;
    let g: &mut Xyz = f;
    match e {
        //~^ ERROR cannot use `e` because it was mutably borrowed [E0503]
        Xyz::A => {}
        Xyz::B => {}
    };
    *g = Xyz::B;
}
