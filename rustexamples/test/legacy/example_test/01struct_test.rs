struct Rectangle {
    width: i32,
    height: i32,
}

fn main() {
    let rect1 : Rectangle = Rectangle {
        width: 30,
        height: 50,
    };
    let area1 : i32 = area(&rect1);
}

fn area(rectangle: &Rectangle) -> i32 {
    return (*rectangle).width * (*rectangle).height;
}
