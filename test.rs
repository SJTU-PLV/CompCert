unsafe extern "C" { fn printf(_ : &mut  [i8], ...) -> i32; }
const __stringlit_1 : [i8;13] = [    b'h' as i8,
    b'e' as i8,
    b'l' as i8,
    b'l' as i8,
    b'o' as i8,
    b' ' as i8,
    b'w' as i8,
    b'o' as i8,
    b'r' as i8,
    b'l' as i8,
    b'd' as i8,
    b'\n' as i8,
    b'\0' as i8
];

fn main()
{
  
   let mut _10000 : i32 /*this is unit */;
   _10000 = printf(__stringlit_1.as_ptr() as &mut  [i8]);
}


