struct S {
    f: Box<i32>,
    g: i32
}


fn main(){
    let mut s1 : Box<S> = Box::new(S{f: Box::new(1), g: 2});
    let s2 : &mut i32 = &mut *((*s1).f);
    printf("%d", (*s1).g);
    printf("%d", *s2);
}

