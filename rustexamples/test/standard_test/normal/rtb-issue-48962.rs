// Repo: rust-lang/rust
// Source: borrowck/borrowck-issue-48962.rs
// After moving a &mut reference, cannot assign through its field

struct IPair { fst: i32, snd: i32 }

fn b() {
    let mut t: IPair = IPair { fst: 22, snd: 44 };
    let mut src: &mut IPair = &mut t;
    let _u1: &mut IPair = src;
    src.fst = 66; //~ ERROR use of moved value: `src` [E0382]
}

fn main() {
    b();
}
