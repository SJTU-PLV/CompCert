// Repo: rust-lang/rust
// Source: nll/borrowed-referent-issue-38899.rs
// Regression test for issue #38899

struct Block<'a> {
    current: &'a i32,
    unrelated: &'a i32,
}

fn bump<'a>(mut block: &mut Block<'a>) {
    let x: &mut &mut Block<'a> = &mut block;
    let _u1: &'a i32 = (*x).current;
    let p: &'a i32 = &*block.current;
    //~^ ERROR cannot borrow `*block.current` as immutable because it is also borrowed as mutable
    let _u2: &mut &mut Block<'a> = x;
    let _u3: &'a i32 = p;
}

fn main() {
    let val: i32 = 1;
    let mut b: Block = Block { current: &val, unrelated: &val };
    bump(&mut b);
}
