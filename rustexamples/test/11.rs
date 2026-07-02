fn main(){
    let mut v: i32 = 1;
    let mut p: &mut i32 = &mut v;
    let mut q: &mut &mut i32 = &mut p;
    v = 2; // invalidate the borrow of q; note that rustc reports error here
    let mut v1: i32 = 3;
    *q = &mut v1; // In our forward-style borrow checker, we do not need to report error here because we just need to ensure the region of p is valid and we do not need to check the region of *q is valid or not
}