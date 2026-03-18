fn main(){
    let mut a: Box<i32> = Box(1);
    let mut p: &mut i32 = &mut *a;
    a = Box(2); //reassingment here which would invalidate p
    *p = 3;
    // printf("%d", *p); // report error here
}