fn choose<'c, 'a, 'b>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32
    where 'a: 'c, 'b: 'c
{
    return &mut *a;
}

fn test_choose(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut p: &mut i32 = choose(&mut v1, &mut v2);
    v2 = 3; // if we uncomment the following line, error would be reported here
    // *p = 4;
}

fn assign<'a, 'b, 'c>(input: &'a mut &'b mut i32, val: &'c mut i32)
    where 'c: 'b
{
    *input = val;
    return;
}

fn test_assign(){
    let mut v: i32 = 2;
    let mut input: &mut i32 = &mut v;
    {
        let mut b: Box<i32> = Box::new(2);
        assign(&mut input, &mut *b);
    }  
    // let mut tmp: i32 = *input; // if uncomment this line, line 27 would be an error
    // printf("Use-after-free of input: %d", *input);
}

fn main() {}
