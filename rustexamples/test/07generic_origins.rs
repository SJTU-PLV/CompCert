fn main() {
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut p: &i32 = &v1;
	let mut q : &i32 = return_ref(p, &v2);
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
