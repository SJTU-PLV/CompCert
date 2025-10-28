fn main(){
    let v: i32 = 1;
    let p: &mut i32 = &mut v;
    *p = 4;
    loop{
        *p = 4; // report error here
        v = 3;
    }
}