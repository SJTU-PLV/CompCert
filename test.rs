pub struct __sFILEX;
unsafe extern "C" { fn scanf(_ : *mut i8, ...) -> i32; }
static mut __stringlit_1 : [i8;3] = [    b'%' as i8,
    b'd' as i8,
    b'\0' as i8
];

fn main(){
  
   unsafe {
   let mut a : &mut  [i32] = Default::default();
   let mut c : i32 = 0;
   let mut _128 : &mut  [std::ffi::c_void] = Default::default();
   let mut _10007 : ();
   let mut _10006 : &mut  [i32] = Default::default();
   let mut _10005 : &mut  [i32] = Default::default();
   let mut _10004 : &mut  [i32] = Default::default();
   let mut _10003 : &mut  [i32] = Default::default();
   let mut _10002 : &mut  [i32] = Default::default();
   let mut _10001 : ();
   let mut _10000 : &mut  [i32] = Default::default();
   let mut _1 : &mut  [i32] = Default::default();
   let mut _2 : &mut  [i32] = Default::default();
   a = &mut [];
   c = (1) as i32;
   scanf(__stringlit_1.as_mut_ptr(), &mut c);
   if c == 1 {
     let mut _128 = vec![i32::default(); (10) as usize].into_boxed_slice();
     a = _128.as_mut();
   }
   if !(a).is_empty() {
     a[(0) as usize] = (0) as i32;
     a[(1) as usize] = (5) as i32;
     a[(2) as usize] = (10) as i32;
     a[(3) as usize] = (a[(1) as usize] + a[(2) as usize]) as i32;
     (_1, _2) = (a).split_at_mut((1 as usize));
     _2[(0_u32) as usize] = (20) as i32;
     /* free call removed, handled by Box drop */;
   }
 }
   
}


