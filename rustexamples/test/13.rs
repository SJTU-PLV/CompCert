fn main(){
    let v: i32 = 1;
    let p: &mut i32 = &mut v;
    let q: &mut i32 = &mut *p;
    v = 4;
    *q = 3;
}