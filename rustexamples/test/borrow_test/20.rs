fn main(){
    let x: i32 = 22;
    let y: i32 = 44;
    let p: & i32 = &x;
    y = y + 1;
    let q: & i32 = &y;
    if x < y {
        p = q;
        x = x + 1;
    } else {
        y = y + 1; // the error should not be reported here
    }
    y = y + 1; // it should be reported here
    printf("%d", *p);
}