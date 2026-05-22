// A Polonius example from https://smallcultfollowing.com/babysteps/blog/2023/09/29/polonius-part-2/

fn main(){
    let mut x: i32 = 22;
    let mut y: i32 = 44;
    let mut p: & i32 = &x;
    y = y + 1;
    let mut q: & i32 = &y;
    if x < y {
        p = q;
        x = x + 1;
    } else {
        // q is not live here, so there should be no error reported
        y = y + 1; 
    }
    y = y + 1; // If we uncomment the following line, error should be reported here
    // let mut tmp: i32 = *p;
    // printf("%d", *p);
}