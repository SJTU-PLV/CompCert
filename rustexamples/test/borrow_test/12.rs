fn main(){
    let v: i32 = 1;
    let dummy1: i32 = 2;
    let dummy2: &mut i32 = &mut dummy1;
    let p: &mut i32 = &mut v;
    let x: &mut &mut i32 = &mut p;
    let tmp: i32 = 2;
    *x = &mut tmp;
    x = &mut dummy2;
    tmp = 3;
    *p = 4; // we report error here
}
