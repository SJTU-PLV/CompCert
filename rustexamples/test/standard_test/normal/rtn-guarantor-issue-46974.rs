// Source: nll/guarantor-issue-46974.rs
// Test that NLL analysis propagates lifetimes correctly through
// field accesses, Box accesses, etc.

struct IPair { fst: i32 }

fn foo(s: &mut IPair) -> i32 {
    let t: &mut IPair = &mut *s; // this borrow should last for the entire function
    let x: &i32 = &t.fst;
    *s = IPair { fst: 2 }; //~ ERROR cannot assign to `*s`
    return *x;
}

fn bar(s: &Box<IPair>) -> &'static i32 {
    return &(**s).fst; //~ ERROR lifetime may not live long enough
}

fn main() {
    let tmp: IPair = IPair { fst: 0 };
    let tmp_box: Box<IPair> = Box::new(IPair { fst: 1 });
    foo(&mut tmp);
    bar(&tmp_box);
}
