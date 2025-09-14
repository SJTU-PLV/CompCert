// Note that the origin environment may be wrong

fn main(){
   let mut v1 = 42;
   let mut v2 = 13;
   let mut m = &mut v1;
   let mut p = &mut m; // 'p1 -> {m} 'p2 -> {v1}
   let mut q = &mut **p; // 'q -> {**p, m, v1} 'p1 -> {m} 'p2 -> {v1}
   *p = &mut v2; // 'q -> {m, v1} 'p1 -> {m} 'p2 -> {v2}
   let mut x = &mut **p; // 'x -> {**p, m, v2} 'q -> {m, v1} 'p1 -> {m} 'p2 -> {v2}
   **p = 13; // 'x -> Dead 'q -> {m, v1} 'p1 -> {m} 'p2 -> {v2}
   println!("{}", *q); // ok, print 42
}

