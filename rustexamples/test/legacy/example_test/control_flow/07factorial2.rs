fn example2() -> Box<i32> {
    let mut n : i32 = 10;
    let mut b : i32 = 1;
    while 0 < n {
        let mut c : Box<i32> = Box(*b);
        *c = (*b) * n;
        n = n - 1;
        b = c;
    }
    return b;
}

fn main() {
	let mut y : Box<i32> = example2();
}