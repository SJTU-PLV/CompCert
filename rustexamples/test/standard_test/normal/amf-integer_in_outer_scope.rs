// Source: borrowck.rs (integer_in_outer_scope test)

fn main() {
    {
        {
            let v: i32 = 0;
            let _: i32 = v;
        }
    }
}
