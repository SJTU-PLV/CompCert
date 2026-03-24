fn main(){
    let mut b: Box<i32> = Box::new(1);
    let mut p: &mut Box<i32> = &mut b; 
    // FIXME: memory leak here because we do not keep drop(*p) after drop elaboration as *p is not a move path. To solve this issue, we need to introduce a new statement drop_and_replace and lower *p = xxx into [temp = xxx (note that we have Sassign, Sassign_box and Sassign_variant...., so it may be better to introduce this temp); drop_and_replace(*p, move temp)]. Only drop(*p) is not enough because borrow checking assumes that all the modification via mutable reference is not destructive, i.e., if it drops the old value, it must replace it with a new value. 
    *p = Box::new(2);
}