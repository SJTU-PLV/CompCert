fn main() {
	let n : i32 = 10;
	let y : Box<i32> = fact(n);
	// printf("Factorial of %d is %d\n", n, *y);
}


fn fact(n:i32) -> Box<i32> {
	let a : i32 = 1;
    let b : Box<i32> = Box::new(1);

	while (true) {
		let c : Box<i32> = Box::new(*b);
		if (0 < n) {
			*c = (*b) * n;
			n = n - 1;
			b = c;
			continue;
		}
		else {
			break;
		}
	}
	return b;
}
