// Repo: rust-lang/a-mir-formality
// Source: borrowck.rs (if_false_borrowck test)

struct Map { value: i32 }

fn foo<'a>(m: &'a mut Map) -> &'a mut Map {
    let n: &mut Map = &mut *m;
    if false {
        return n;
    } else {
        let o: &mut Map = &mut *m;
        return o;
    }
}

fn main() {
    let mut m: Map = Map { value: 1 };
    let _: &mut Map = foo(&mut m);
}
