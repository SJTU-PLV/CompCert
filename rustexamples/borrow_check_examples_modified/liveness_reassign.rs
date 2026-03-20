fn main(){
    let mut a : Box<i32> = Box::new(1);
    let mut r : &mut Box<i32> = &mut a;
    let p : &mut &mut Box<i32> = &mut r;
    let mut b : Box<i32> = Box::new(2);
    *p = &mut b;
    *b = 3;
    **r = 4;
}