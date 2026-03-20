fn main(){
    // let x be a box and equal to 5
    let x: Box<i32> = Box::new(1);
    // init y
    let a: Box<i32>;
    let y: Box<i32>;
    // if x is less than 10
    if *x < 10 {
        // y is equal to x
        y = Box::new(3);
    }
    // else
    else {
        // y is equal to 10
        a = Box::new(10);
    }
}