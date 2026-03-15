fn main() {
	let a : i32 = 2;
	let b : &mut i32 = &mut a;
	*b = 3;
}