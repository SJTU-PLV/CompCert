// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (continue_drops_borrowed_local_loop_carried test)

fn main() {
    let mut r: &i32;
    loop {
        let _: i32 = *r; // in later iterations, reads from dropped y
        let y: i32 = 0;
        r = &y;
        continue; // y drops here — r may point to dropped value
    }
}
