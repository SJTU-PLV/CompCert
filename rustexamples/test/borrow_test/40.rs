fn main(){
    let b: Box<i32> = Box(1);
    let p: &mut Box<i32> = &mut b; // FIXME: memory leak here because we do not generate drop(*p) for now. But I think leaking is not UB.
    *p = Box(2);
}