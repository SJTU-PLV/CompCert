fn main()
{
  
   let mut abcd : [i32;32];
   let mut a : &mut  [i32];
   let mut b : &mut  [i32];
   let mut c : &mut  [i32];
   let mut d : &mut  [i32];
   (_1, _2) = split_at_mut(a as (), 0 as ());
   a = _2;
   (_3, _4) = split_at_mut(abcd as (), 8 as ());
   b = _4;
   (_5, _6) = split_at_mut(_4 as (), 8 as ());
   c = _6;
   (_7, _8) = split_at_mut(_6 as (), 8 as ());
   d = _8;
}


