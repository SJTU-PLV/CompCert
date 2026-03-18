fn main(){
    let mut b: Box<i32> = Box(1);
    let mut a: Box<i32> = b;
    let mut p: &mut Box<i32> = &mut a;
    let mut tmp: i32 = **p;
    // printf("p is %d", *p);
}