
// an example from the Rust documentation
// https://rust-lang.github.io/rfcs/0320-nonzeroing-dynamic-drop.html

// Define a struct `Pair` with two fields `x` and `y`
struct Pair {
    x: Box<i32>,
    y: Box<i32>,
}

enum Option{
    Some(i32),
    None
}

fn test(){

}

fn f2(){
    // not supporting 
    let pDD: Pair;
    pDD.x = Box::new(1);
    pDD.y = Box::new(2);
    let pDS : Pair; 
    let some_d : Option;
    if test() {
        {
            let temp : Box<i32> = pDD.x;
            some_d = Option::Some(1);
        }
    } else {
        pDD.y = pDD.x;
        some_d = Option::None;
        pDS.x = Box::new(3);
    }
}

fn main(){
    f2();
    printf("Success\n");
}
