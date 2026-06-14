// Repo: rust-lang/rust
// Source: borrowck/borrowck-uniq-via-ref.rs
// Positive test: borrowing through Box via various reference paths (&mut -> &imm OK)

struct Rec {
    f: Box<i32>
}

struct Outer {
    f: Inner
}

struct Inner {
    g: Innermost
}

struct Innermost {
    h: Box<i32>
}

fn borrow(_v: &i32) {}

fn box_mut(v: &mut Box<i32>) {
    borrow(&**v);
}

fn box_mut_rec(v: &mut Rec) {
    borrow(&*v.f);
}

fn box_mut_recs(v: &mut Outer) {
    borrow(&*v.f.g.h);
}

fn box_imm(v: &Box<i32>) {
    borrow(&**v);
}

fn box_imm_rec(v: &Rec) {
    borrow(&*v.f);
}

fn box_imm_recs(v: &Outer) {
    borrow(&*v.f.g.h);
}

fn main() {
    let mut b1: Box<i32> = Box::new(42);
    let mut r: Rec = Rec { f: Box::new(1) };
    let mut o: Outer = Outer { f: Inner { g: Innermost { h: Box::new(2) } } };
    box_mut(&mut b1);
    box_mut_rec(&mut r);
    box_mut_recs(&mut o);
    box_imm(&b1);
    box_imm_rec(&r);
    box_imm_recs(&o);
}
