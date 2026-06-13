// Source: borrowck/borrowck-uniq-via-lend.rs

fn borrow(_v: &i32) {}

struct RecF { f: Box<i32> }

struct RecsF { f: RecsG }
struct RecsG { g: RecsH }
struct RecsH { h: Box<i32> }

fn local() {
    let mut v: Box<i32> = Box::new(3);
    borrow(&*v);
}

fn local_rec() {
    let mut v: RecF = RecF { f: Box::new(3) };
    borrow(&*v.f);
}

fn local_recs() {
    let mut v: RecsF = RecsF { f: RecsG { g: RecsH { h: Box::new(3) } } };
    borrow(&*v.f.g.h);
}

fn aliased_imm() {
    let mut v: Box<i32> = Box::new(3);
    let w: &Box<i32> = &v;
    borrow(&*v);
    let _u1: &Box<i32> = w;
}

fn aliased_mut() {
    let mut v: Box<i32> = Box::new(3);
    let w: &mut Box<i32> = &mut v;
    borrow(&*v); //~ ERROR cannot borrow `*v`
    let _u1: &mut Box<i32> = w;
}

fn aliased_other() {
    let mut v: Box<i32> = Box::new(3);
    let mut w: Box<i32> = Box::new(4);
    let x: &mut Box<i32> = &mut w;
    borrow(&*v);
    let _u1: &mut Box<i32> = x;
}

fn aliased_other_reassign() {
    let mut v: Box<i32> = Box::new(3);
    let mut w: Box<i32> = Box::new(4);
    let mut x: &mut Box<i32> = &mut w;
    x = &mut v;
    borrow(&*v); //~ ERROR cannot borrow `*v`
    let _u1: &mut Box<i32> = x;
}

fn main() {
    local();
    local_rec();
    local_recs();
    aliased_imm();
    aliased_mut();
    aliased_other();
    aliased_other_reassign();
}
