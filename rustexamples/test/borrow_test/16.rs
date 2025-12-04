fn main(){
    let v: i32 = 1;
    let dummy1: i32 = 2;
    let dummy2: i32 = 2;
    let p: &mut i32 = &mut dummy1;
    let q: &mut i32 = &mut dummy2;
    if true {
        p = &mut v;
    }
    else{
        q = &mut v;
    }
    v = 4;
    // printf("%d", *p);
    let tmp: i32 = *p;
}
