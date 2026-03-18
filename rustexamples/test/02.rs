fn main() {
	let mut a : i32 = 2;
	let mut b : &mut i32 = &mut a;
	*b = 3;
}