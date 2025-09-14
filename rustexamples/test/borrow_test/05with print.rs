fn main() {
	let a : i32 = 2;
	let r1 : &i32 = &a;
	let r2 : &mut i32 = &mut a;
    printf("%d and %d", *r1, *r2); // report error here
}