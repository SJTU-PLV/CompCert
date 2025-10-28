fn main(){
    let b: Box<i32> = Box(1);
    let a: Box<i32> = b;
    let p: &mut Box<i32> = &mut b;
    printf("p is %d", *p);
}