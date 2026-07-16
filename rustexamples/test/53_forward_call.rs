fn test<'a>(x: &'a mut i32, y: &'a mut i32) {
    *x = 1;
    *y = 2;
    // return &mut *x;
}

fn main(){
    let mut v: i32 = 1;
    // let mut x: &mut i32 = &mut v;
    test(&mut v, &mut v);
    // *x = 2;
}