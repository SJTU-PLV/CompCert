struct A<'a>;

struct A<'a>{
    x: &'a mut i32,
    y: i32
}

fn main(){
    let v: i32 = 1;
    let a: A = A {x: &mut v, y: 3};
    a.x = &mut a.y;
    let p: &mut i32 = &mut *a.x;
    // let p: &mut i32 = &mut a.y; // This line also cause error because 'a which contain {a.y} is live and we deeply access a.y
    let b: A = a; // error! If we uncomment this line, there would be no error
}