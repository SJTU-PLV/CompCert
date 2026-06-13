// Source: borrowck/borrowck-uninit-ref-chain.rs

struct S {
    x: i32,
    y: i32
}

struct SRef {
    x: & &i32,
    y: & &i32
}

fn main() {
    let x1: & &Box<i32>;
    let _y1: &Box<i32> = &**x1; //~ ERROR [E0381]

    let x2: & &S;
    let _y2: &S = &**x2; //~ ERROR [E0381]

    let x3: & &i32;
    let _y3: &i32 = &**x3; //~ ERROR [E0381]

    let mut a1: S;
    a1.x = 0; //~ ERROR [E0381]
    let _b1: &i32 = &a1.x;

    let mut a2: SRef;
    a2.x = & &0; //~ ERROR [E0381]
    let _b2: &i32 = &**a2.x;

    let mut a3: S;
    a3.x = 0; //~ ERROR [E0381]
    let _b3: &i32 = &a3.y;

    let mut a4: SRef;
    a4.x = & &0; //~ ERROR [E0381]
    let _b4: &i32 = &**a4.y;
}
