fn main() {
	let a : i32 = 2;
	let b : &mut i32 = &mut a;
    *b = 4;
    a = 3;
    printf("%d", *b); // report error here
}