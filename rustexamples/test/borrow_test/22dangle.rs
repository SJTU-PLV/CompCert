fn dangle<'a>(x: &'a i32) -> &'a i32{
    let v: i32 = 3;
    if v > *x {
        return &v; // report error here
    }
    else{
        return x;
    }
}

fn main(){
    let v: i32 = 2;
    let r: &i32 = dangle(&v);
    // printf("%d", *r);
}