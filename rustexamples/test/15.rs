fn main(){
    let v: Box<i32> = Box(12);
    let p: &mut i32 = &mut *v;
    let v1: Box<i32> = v;
    *p = 5;
}