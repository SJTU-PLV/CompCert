fn main(){
    let mut v: i32 = 1;
    let mut p: &mut i32 = &mut v;
    let mut q: &mut &mut i32 = &mut p;
    v = 2; // invalidate the borrow of q; note that rustc reports error here
    let mut v1: i32 = 3;
    *q = &mut v1; // cannot use q here; we report error here; what if we change mutable reference to immutable reference?
}