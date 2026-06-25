fn test<'a, 'b, 'c>(mut x: &'a mut i32, mut y: &'b mut i32, mut z: &'c mut i32) 
    -> &'a mut i32 where 'b: 'a, 'c: 'b{
    // 'a:{L('a)} 'b:{L('b)} 'c:{L('c)}
    if true {
        x = &mut *y; // flow L('b) to 'a
        // 'a:{L('a), L('b), *y} 'b:{L('b)} 'c:{L('c)}
    } else {
        y = &mut *z; // flow L('c) to 'b
        // 'a:{L('a)} 'b:{L('b), L('c), *z} 'c:{L('c)}
    }
    // merge: 'a:{L('a), L('b), *y}, 'b:{L('b), L('c), *z}, 'c:{L('c)}
    // kill internal loans: 'a:{L('a), L('b)}, 'b:{L('b), L('c)}, 'c:{L('c)}
    return &mut *x;
}

fn main(){

}