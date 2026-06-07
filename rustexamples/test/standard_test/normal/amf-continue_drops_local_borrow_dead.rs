// Source: borrowck.rs (continue_drops_local_borrow_dead test)

fn main() {
    loop {
        let x: i32 = 0;
        let r: &i32 = &x;
        let _: i32 = *r; // last use of r — borrow ends here
        continue; // r is dead, x can be safely dropped
    }
}
