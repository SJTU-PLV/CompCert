unsafe extern "C" { fn printf(_ : &mut  [i8], ...) -> i32; }
const __stringlit_1 : [i8;6] = [    b'd' as i8,
    b'o' as i8,
    b'n' as i8,
    b'e' as i8,
    b'\n' as i8,
    b'\0' as i8
];

fn main(){
  
   let mut _10000 : ();
   _10000 = printf(__stringlit_1 as &mut  [i8]);
}


