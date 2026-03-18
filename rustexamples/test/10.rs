fn main() {
	let mut v1 : i32 = 2;
	let mut p : &mut i32 = &mut v1;
    let mut v2 : i32 = 4;
    let mut q : &mut i32 = &mut v2;
    v1 = 3;
    // printf("%d", *q);
}