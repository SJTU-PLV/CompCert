fn main() {

	let reference_to_nothing : i32 = no_dangle();
	
	}
	
fn no_dangle() -> i32 {
	let a : i32 = 2;
	return a;
}