// Example to test time-traveling in Polonis

fn main(){
    let mut v = 1;
    let mut a = 2;
    let mut b = 3;
    let mut x = &mut a;
    let mut p = &mut v;
    let mut q = &mut p;
    *q = &mut *x;
    // *x = 16;
    // **q = 15;
    x = &mut b;
    *q = &mut *x; // I think this is the problem of time-traveling concerned by Polonius.
                  // The loan *x must be flowed backward to line 9 where the invariance between 'q2 and 'p is established,
                  // and then *x can be flowed to line 18. That is why accessing *x at line 17 is considered error.
                  // But what Polonius want to handle is that if they want to embed the computation of gen/kill loans in the 
                  // loan analysis via graph reachability, then the backward traversal must be continued if we encounter killing a loan,
                  // i.e., killing *x at line 13, so that the loan *x  can be flowed to p.
    *x = 15; //error reported here
    *p = 13;
}