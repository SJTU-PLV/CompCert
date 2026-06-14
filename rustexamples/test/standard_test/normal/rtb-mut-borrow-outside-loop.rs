// Repo: rust-lang/rust
// Source: borrowck/mut-borrow-outside-loop.rs
// ensure borrowck messages are correct outside special case

fn main() {
    let mut void: () = ();

    let first: &mut () = &mut void;
    let second: &mut () = &mut void; //~ ERROR cannot borrow
    let _u1: &mut () = first;
    let _u2: &mut () = second;

    loop {
        let mut inner_void: () = ();

        let inner_first: &mut () = &mut inner_void;
        let inner_second: &mut () = &mut inner_void; //~ ERROR cannot borrow
        let _u3: &mut () = inner_second;
        let _u4: &mut () = inner_first;
    }
}
