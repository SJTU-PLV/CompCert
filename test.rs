#[path = "runtime/ptr.rs"]
mod ptr;
use ptr::*;
pub struct __sFILEX;
unsafe extern "C" { fn scanf(_ : Ptr<i8>, ...) -> i32; }
static mut __stringlit_1 : [i8;3] = [    b'%' as i8,
    b'd' as i8,
    b'\0' as i8
];

fn foo(mut abcd: Ptr<i32>)

{
  let mut a : Ptr<i32> = Ptr::null();
  let mut b : Ptr<i32> = Ptr::null();
  let mut c : Ptr<i32> = Ptr::null();
  let mut d : Ptr<i32> = Ptr::null();
  let mut _10002 : Ptr<i32> = Ptr::null();
  let mut _10001 : Ptr<i32> = Ptr::null();
  let mut _10000 : Ptr<i32> = Ptr::null();
  a = abcd.add((0) as usize);
  b = abcd.add((8) as usize);
  c = abcd.add((16) as usize);
  d = abcd.add((24) as usize);
  b.store((1) as usize, 42);
  abcd.store((10) as usize, 100);
  d.store((3) as usize, 44);

  
}

fn main(){
  
   let mut abcd = [0; 32];
   let mut a : Ptr<i32> = Ptr::null();
   let mut c : i32 = 0;
   let mut _128 : Ptr<std::ffi::c_void> = Ptr::null();
   let mut _10007 : Ptr<i32> = Ptr::null();
   let mut _10006 : Ptr<i32> = Ptr::null();
   let mut _10005 : Ptr<i32> = Ptr::null();
   let mut _10004 : Ptr<i32> = Ptr::null();
   let mut _10003 : Ptr<i32> = Ptr::null();
   let mut _10001 : Ptr<i32> = Ptr::null();
   foo(Ptr::from_ref(&mut abcd));
   a = Ptr::null();
   c = (1) as i32;
   c = read_i32_with_default(c);
   if c == 1 {
     
     a = Ptr::<i32>::alloc((10) as usize);
   }
   if !(a).is_null() {
     a.store((0) as usize, 0);
     a.store((1) as usize, 5);
     a.store((2) as usize, 10);
     a.store((3) as usize, a.load((1) as usize) + a.load((2) as usize));
     a = a.add((1) as usize);
     a.store((1) as usize, 20);
     a.free();
   }
 
   
}

fn read_i32_with_default(default: i32) -> i32 {
  let mut value = default;
  unsafe {
    let fmt = Ptr::from_ref(&mut __stringlit_1[..]);
    let value_slice = core::slice::from_mut(&mut value);
    let value_ptr = Ptr::from_ref(value_slice);
    scanf(fmt, value_ptr);
  }
  value
}

