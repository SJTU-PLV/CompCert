fn main(){
    let mut a: Box<i32> = Box::new(1);
    let mut p: &mut i32 = &mut *a;
    a = Box::new(2); //reassingment here which would invalidate p
    *p = 3;
    // printf("%d", *p); // report error here
}