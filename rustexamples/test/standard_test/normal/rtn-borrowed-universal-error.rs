// Source: nll/borrowed-universal-error.rs
// Cannot return value referencing temporary value

struct IPair { fst: i32 }

fn gimme(x: &IPair) -> &i32 {
    return &x.fst;
}

fn foo<'a>() -> &'a i32 {
    let v: i32 = 22;
    return gimme(&IPair { fst: v });
    //~^ ERROR E0515 cannot return value referencing temporary value
}

fn main() {
    let _u1: &i32 = foo();
}
