fn main() {
	let mut a : i32 = 2;
	let mut r1 : &i32 = &a;
	let mut r2 : &mut i32 = &mut a;
    // printf("%d and %d", *r1, *r2); // report error here
}