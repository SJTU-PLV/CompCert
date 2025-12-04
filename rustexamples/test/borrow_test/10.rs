fn main() {
	let v1 : i32 = 2;
	let p : &mut i32 = &mut v1;
    let v2 : i32 = 4;
    let q : &mut i32 = &mut v2;
    v1 = 3;
    // printf("%d", *q);
}