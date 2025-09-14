const __stringlit_1 : [i8;4] = [    b'%' as i8,
    b'd' as i8,
    b'\n' as i8,
    b'\0' as i8
];

fn f(x: i32)
 -> i32
{
  let mut _10000 : i32;
  _10000 = x;
  return _10000;
}

fn main()
{
  
   let mut b : i32;
   let mut _128 : i32;
   let mut _10000 : i32 /*this is unit */;
   _128 = f(3 as i32);
   b = _128;
   println!("{}\n", b);
}


