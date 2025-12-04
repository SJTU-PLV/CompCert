fn main() {
    let v1: i32 = 1;
    let v2: i32 = 2;
    let p: &i32 = &v1;
	let q : &i32 = return_ref(p, &v2);
    // printf("%d", *q);
}

fn return_ref<'a, 'b, 'c>(x: &'a i32, y: &'b i32) -> &'c i32 
    where 'b: 'c, 'a: 'c
{
    if *x > 3 {
        return &*x;
    } else {
        return &*y;
    }
    return &*x;
}
