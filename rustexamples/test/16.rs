fn main(){
    let mut v: i32 = 1;
    let mut dummy1: i32 = 2;
    let mut dummy2: i32 = 2;
    let mut p: &mut i32 = &mut dummy1;
    let mut q: &mut i32 = &mut dummy2;
    if true {
        p = &mut v;
    }
    else{
        q = &mut v;
    }
    v = 4;
    // printf("%d", *p);
    let mut tmp: i32 = *p;
}
