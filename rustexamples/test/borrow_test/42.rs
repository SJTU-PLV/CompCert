fn main(){
    let v: i32 = 1;
    let x: &mut i32 = &mut v;
    x = &mut *x;
    *x = 3;
}