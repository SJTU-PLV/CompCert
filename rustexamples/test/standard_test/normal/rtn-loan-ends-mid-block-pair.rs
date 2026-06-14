// Source: nll/loan_ends_mid_block_pair.rs
// Mut borrow of struct field ends mid-block after capitalize, then mutation OK

struct IPair { fst: i32, snd: i32 }

fn capitalize(c: &mut i32) {
    *c = *c + 1;
}

fn nll_fail() {
    let mut data: IPair = IPair { fst: 1, snd: 2 };
    let c: &mut i32 = &mut data.fst;
    capitalize(&mut *c);
    data.fst = 3;
    //~^ ERROR E0506 cannot assign to `data.fst` because it is borrowed
    data.fst = 4;
    capitalize(c);
}

fn nll_ok() {
    let mut data: IPair = IPair { fst: 1, snd: 2 };
    let c: &mut i32 = &mut data.fst;
    capitalize(c);
    data.fst = 3;
    data.fst = 4;
}

fn main() {
    nll_fail();
    nll_ok();
}
