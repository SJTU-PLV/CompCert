#[path = "/Users/yaodongdong/WorkPlace/project/Compcert/runtime/ptr.rs"]
mod ptr;
use ptr::*;
#[path = "/Users/yaodongdong/WorkPlace/project/Compcert/runtime/callback.rs"]
mod callback;
pub struct __sFILEX;
static mut __stringlit_1 : [i8;4] = [    b'%' as i8,
    b'd' as i8,
    b' ' as i8,
    b'\0' as i8
];

extern "C" fn f1(mut ar: Ptr<i32>, mut n: i32)

{
  unsafe {
  let mut i: i32 = 0;
  let mut br: Ptr<i32> = Ptr::null();
  i = (0) as i32;
  loop {
    if !(i < ((n) as i32) - ((1) as i32)) {
      break;
    }
    br = (ar.clone()).offset((1) as isize);
    ar.store(0, (((br.clone()).load(0)) as i32));
    i = (((i) as i32) + ((1) as i32)) as i32;
  }
}
  
}

fn main(){
  
   unsafe {
   let mut ar: [i32; 5] = array_default::<i32, 5>();
   let mut i: i32 = 0;
   let mut _10004: Ptr<i32> = Ptr::null();
   let mut _10003: Ptr<i32> = Ptr::null();
   let mut _10002: Ptr<i32> = Ptr::null();
   let mut _10001: Ptr<i32> = Ptr::null();
   let mut _10000: Ptr<i32> = Ptr::null();
   (Ptr::from_ref(&mut ar[..]).offset((0) as isize)).store(0, ((1) as i32));
   (Ptr::from_ref(&mut ar[..]).offset((1) as isize)).store(0, ((2) as i32));
   (Ptr::from_ref(&mut ar[..]).offset((2) as isize)).store(0, ((3) as i32));
   (Ptr::from_ref(&mut ar[..]).offset((3) as isize)).store(0, ((4) as i32));
   (Ptr::from_ref(&mut ar[..]).offset((4) as isize)).store(0, ((5) as i32));
   f1(unsafe { (Ptr::from_ref(&mut ar)).cast::<i32>() }, (5) as i32);
   i = (0) as i32;
   loop {
     if !(i < 5) {
       break;
     }
     unsafe {
       __libc_printf(Ptr::from_ref(&mut __stringlit_1[..]).as_ptr(),
       ar.load((i) as usize));
       };
     i = (((i) as i32) + ((1) as i32)) as i32;
   }
 }
   
}

extern "C" {
  #[link_name = "printf"]
  fn __libc_printf(fmt: *const i8, ...) -> i32;
}
fn print_c_string(fmt: Ptr<i8>) -> i32 {
  unsafe {
    __libc_printf(fmt.as_ptr())
  }
}

