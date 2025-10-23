fn main()
{
  
   let mut abcd : [i32;32];
   let mut n : i32;
   let mut a : &mut  [i32];
   let mut b : &mut  [i32];
   let mut c : &mut  [i32];
   let mut d : &mut  [i32];
   let mut _10008 : &mut  [i32];
   let mut _10007 : &mut  [i32];
   let mut _10006 : &mut  [i32];
   let mut _10005 : &mut  [i32];
   let mut _10004 : &mut  [i32];
   let mut _10003 : &mut  [i32];
   let mut _10002 : &mut  [i32];
   let mut _10001 : &mut  [i32];
   let mut _10000 : &mut  [i32];
   abcd[0 as usize] = 1;
   abcd[1 + 2 as usize] = 2;
   n = 3;
   abcd[n as usize] = 3;
   abcd[n + 4 as usize] = 4;
   abcd[1 + 2 + 3 as usize] = 100;
   (_1, _2) = split_at_mut(abcd, 0_u32);
   (_3, _4) = split_at_mut(_2, 8_u32);
   (_5, _6) = split_at_mut(_4, 8_u32);
   (_7, _8) = split_at_mut(_6, 8_u32);
   b = _5;
   d = _8;
   a = _3;
   c = _7;
   b[1 as usize] = 42;
   c[2 as usize] = 43;
   _5[2_u32 as usize] = 100;
   d[3 as usize] = 44;
}


