fn main(){
    let mut v: i32 = 1;
    let mut p: &mut i32 = &mut v;
    let mut q: &mut i32 = &mut *p;
    v = 4;
    *q = 3;
}