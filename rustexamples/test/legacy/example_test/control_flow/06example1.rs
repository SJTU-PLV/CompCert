fn example1(a: i32, b: Box<i32>) {
    a = *b;
    let mut c : Box<i32>;
    if a < *b {
        c = b;
    }
    else {
        b = Box(3);
    }
}

fn main() {
    let mut a : i32 = 2;
    let mut b : Box<i32> = Box(1);
    example1(a,b);
    example1(a,b);
}