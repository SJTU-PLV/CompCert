fn main() {
	let y : Box<i32> = example3();
}


fn example3() -> Box<i32> {
    let n : i32 = 10;
	let a : i32 = 1;
    let b : Box<i32> = Box(1);

	while true {
		let c : Box<i32> = Box(*b);
		if 0 < n {
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

