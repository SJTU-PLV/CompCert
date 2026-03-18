fn main(){
    let mut v: Box<i32> = Box(12);
    let mut p: &mut i32 = &mut *v;
    let mut v1: Box<i32> = v;
    *p = 5;
}