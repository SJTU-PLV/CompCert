fn main() {
	let mut a : i32 = 2;
	
	{
		let mut r1 : &mut i32 = &mut a;
	}
	*r1 = 3;
	let mut r2 : &mut i32 = &mut a;
}