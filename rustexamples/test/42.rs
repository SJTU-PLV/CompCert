fn main(){
    let mut v: i32 = 1;
    let mut x: &mut i32 = &mut v;
    x = &mut *x;
    *x = 3;
}