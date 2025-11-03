pub struct __sFILEX;
fn main(){
  
   unsafe {
   let mut a : &mut  [i32];
   let mut _128 : &mut  [std::ffi::c_void];
   let mut _10004 : ();
   let mut _10003 : &mut  [i32];
   let mut _10002 : &mut  [i32];
   let mut _10001 : &mut  [i32];
   let mut _10000 : &mut  [i32];
   let mut _1 : &mut  [i32];
   let mut _2 : &mut  [i32];
   let mut _128 = vec![i32::default(); (10) as usize].into_boxed_slice();
   a = (&mut _128 as &mut  [i32]);
   a[(1) as usize] = (5) as i32;
   a[(2) as usize] = (10) as i32;
   a[(3) as usize] = (a[(1) as usize] + a[(2) as usize]) as i32;
   (_1, _2) = (a).split_at_mut((1 as usize));
   _2[(0_u32) as usize] = (20) as i32;
   /* free call removed, handled by Box drop */;
 }
   
}


