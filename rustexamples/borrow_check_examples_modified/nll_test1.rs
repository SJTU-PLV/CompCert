fn main(){
    let mut v : i32 = 1;
    let mut tmp : i32 = 2;
    let mut p : &mut i32 = &mut v;
    let mut q : &mut i32 = &mut *p; 
    p = &mut tmp; 
    *q = 5; 
    v = 4;
    *p = 3; 
}