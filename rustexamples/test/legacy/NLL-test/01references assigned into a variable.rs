fn main() {
	let mut a : i32 = 1;
	let mut b : &mut i32 = &mut a;
	let mut c : &mut i32 = b;
	*c = *c + 1;
	*b = *b + 1;
    printf("%d", a);
}