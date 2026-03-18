fn main(){
    let mut v: i32 = 1;
    let mut p: &mut i32 = &mut v;
    *p = 4;
    loop{
        *p = 4; // report error here
        v = 3;
    }
}