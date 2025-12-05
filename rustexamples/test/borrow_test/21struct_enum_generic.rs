struct A<'a,'b> where 'a: 'b {
    x: &'a i32,
    y: &'b i32
}

enum B<'a, 'b, 'c> where 'a: 'b, 'a: 'c {
    f(&'a i32),
    g(&'b i32, &'c i32)
}

fn main(){
    let v1: i32 = 1;
    let v2: i32 = 2;
    let a: A = A { x: &v1, y: &v2};
    let b: B = B::f(&v1);
    match b {
        B::f(r) => {
            let tmp1: i32 = *r;
        }
        B::g(r1, r2) => {
            let tmp2: i32 = *r1;
            let tmp3: i32 = *r2;
            // printf("%d and %d\n", *r1, *r2);
        }
    };
    let tmp4: i32 = *(a.x);
    // printf("%d\n", *(a.x));
}