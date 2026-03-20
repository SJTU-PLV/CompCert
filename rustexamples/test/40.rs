fn main(){
    let mut b: Box<i32> = Box::new(1);
    let mut p: &mut Box<i32> = &mut b; // FIXME: memory leak here because we do not generate drop(*p) for now. But I think leaking is not UB.
    *p = Box::new(2);
}