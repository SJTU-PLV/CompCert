fn dangle<'a>(x: &'a i32) -> &'a i32{
    let mut v: i32 = 3;
    if v > *x {
        return &v; // report error here
    }
    else{
        return x;
    }
}

fn main(){
    let mut v: i32 = 2;
    let mut r: &i32 = dangle(&v);
    // printf("%d", *r);
}