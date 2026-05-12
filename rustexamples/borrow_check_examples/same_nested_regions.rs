// Used to test when x and y share the same nested region, if we let
// *x points to *z, then does Polonius consider *y and *z are aliased?
fn test<'a, 'b, 'd>(mut x: &'a mut &'b mut i32, mut y: &'a mut &'b mut i32, mut z: &'d mut i32) {
    *x = &mut *z;
    *z = 3;
    // **y = 3; // error
}

fn main(){

}