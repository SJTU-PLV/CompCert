enum List<'a, 'b> {
    Dummy(&'b mut i32),
    Cons(&'a mut i32, Box<List<'a, 'b>>),
}

enum List1<'a, 'b> {
    Dummy(&'b mut i32),
    Cons(Box<&'a mut i32>, Box<List1<'a, 'b>>),
}

fn main() {
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut v3: i32 = 3;
    let mut x: i32 = 1;
    let mut y: i32 = 2;

    let l0 = List::Cons(&mut v1, Box::new(List::Dummy(&mut x)));
    let l1 = List::Cons(Box::new(&mut v2), Box::new(l0));

    match l1 {
        List::Dummy(_) => {
            v3 = 4;
        }
        List::Cons(r, _) => {
            x = 2;
            *r = 5;
        }
    };

    printf("%d, %d, %d", v1, v2, v3);
}

fn test_list1() {
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut v3: i32 = 3;
    let mut x: i32 = 1;
    let mut y: i32 = 2;

    let l0 : List1 = List1::Cons(Box::new(&mut v1), Box::new(List1::Dummy(&mut x)));
    let l1 : List1 = List1::Cons(Box::new(&mut v2), Box::new(l0));

    match l1 {
        List1::Dummy(_) => {
            v3 = 4;
        }
        List1::Cons(r, _) => {
            *r = 5;
        }
    };

    printf("%d, %d, %d", v1, v2, v3);
}
