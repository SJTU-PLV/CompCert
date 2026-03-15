fn main() {
	let a : i32 = 2;
	
	{
		let r1 : &mut i32 = &mut a;
	}
	*r1 = 3;
	let r2 : &mut i32 = &mut a;
}