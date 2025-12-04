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
        // q is not live here, so there should be no error reported
        y = y + 1; 
    }
    y = y + 1; // If we uncomment the following line, error should be reported here
    // let tmp: i32 = *p;
    // printf("%d", *p);
}