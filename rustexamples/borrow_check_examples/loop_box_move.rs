fn main(){
    // let mut v : Box<i32>;
    // let mut tmp = 12;
    // let mut p = &mut tmp;
    // loop {
    //     v = Box::new(1); // error
    //     // *v = 3;
    //     *p = 2;
    //     p = &mut *v;
    // }
}

fn loop_box_move(){
    let mut v = Box::new(1);
    let mut x = Box::new(2);
    loop{
        v = Box::new(3);
        *v = 4;
        *x = 5;
        x = v;
    }
}

fn is_box_in_one_block_correct(){
    let mut v = Box::new(1);
    let mut x = Box::new(2);
    let mut tmp = 13;
    let mut p = &mut tmp;
    loop {
        v = Box::new(1);
        *v = 3;
        *p = 4;
        x = v;
        p = &mut *x;
    }
}

fn ref_in_box(){
    let mut a = 1;
    let mut b = 2;
    let mut v : Box<&mut i32>;
    let mut tmp = 13;
    let mut x : Box<&mut i32> = Box::new(&mut tmp);
    loop {
        v = Box::new(&mut a);
        // b = 3;
        **x = 5;
        **v = 4;
        x = v;
        *x = &mut b;
    }
}