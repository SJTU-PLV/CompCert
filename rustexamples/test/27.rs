fn return_bor_or_modify<'a>(x: &'a mut i32) -> &'a mut i32{
    if *x > 3 {
        let r : &mut i32 = &mut *x;
        return r;
    }
    *x = 4;
    return x;
}