fn main(){
    let v: i32 = 1;
    let p: &mut i32 = &mut v;
    let q: &mut &mut i32 = &mut p;
    v = 2; // invalidate the borrow of q; note that rustc reports error here
    let v1: i32 = 3;
    *q = &mut v1; // cannot use q here; we report error here; what if we change mutable reference to immutable reference?
}