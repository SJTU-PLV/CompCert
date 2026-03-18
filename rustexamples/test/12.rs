fn main(){
    let mut v: i32 = 1;
    let mut dummy1: i32 = 2;
    let mut dummy2: &mut i32 = &mut dummy1;
    let mut p: &mut i32 = &mut v;
    let mut x: &mut &mut i32 = &mut p;
    let mut tmp: i32 = 2;
    *x = &mut tmp;
    x = &mut dummy2;
    tmp = 3;
    *p = 4; // we report error here
}
