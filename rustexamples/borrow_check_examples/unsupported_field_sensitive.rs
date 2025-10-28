// This program is not supported because of the limitation of the
// reborrow mechanism (i.e., directly flowing the [p] to the region of y)
// rustc +nightly unsupported_field_sensitive.rs -Z polonius=next
fn main(){
    let mut p = (12, 13);
    let mut x = &mut p;
    let mut y = &mut (*x).0;
    p.1 = 15;
    println!("{}", y);
}