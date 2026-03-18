struct A<'a>;

struct A<'a>{
    x: &'a mut i32,
    y: i32
}

fn main(){
    let mut v: i32 = 1;
    let mut a: A = A {x: &mut v, y: 3};
    a.x = &mut a.y;
    let mut p: &mut i32 = &mut *a.x;
    // let mut p: &mut i32 = &mut a.y; // This line also cause error because 'a which contain {a.y} is live and we deeply access a.y
    let mut b: A = a; // error! If we uncomment this line, there would be no error
}