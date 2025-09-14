fn test<'a, 'b:, 'c, 'd>(mut x: &'a mut &'b mut i32, mut y: &'c mut &'d mut i32) 
-> &'b mut i32{
    x = y;
    *x 
}

// This function should be rejected by the borrow checker. We should add lifetime constraints as the following:

// fn test<'a: 'b, 'b: 'd, 'c: 'a, 'd: 'b>(mut x: &'a mut &'b mut i32, mut y: &'c mut &'d mut i32) 
// -> &'b mut i32{
//     x = y;
//     *x 
// }