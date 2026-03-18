fn main() {
	let mut a : i32 = 2;
	let mut b : &mut i32 = &mut a;
    *b = 4;
    a = 3;
    // printf("%d", *b); // report error here
}