enum list_node {
    None,
    Some(Box<list>)
}

struct list {
    value: i32,
    next: list_node
}

fn sum<'a>(mut l: &'a mut list) -> i32 {
    let mut result: i32 = 0;
    loop {
        result = result + (*l).value;
        match (*l).next {
            list_node::Some(ref mut r) => {
                l = &mut **r; // strong update which kills loans that are children of l
            }
            list_node::None => {
                return result;
            }
        }
    }
    return result;
}


fn main(){
    let mut l0: list = list {value: 1, next: list_node::None};
    let mut l1: list = list {value: 2, next: list_node::Some(Box::new(l0))};
    let mut l2: list = list {value: 3, next: list_node::Some(Box::new(l1))};
    let mut res: i32 = sum(&mut l2);
    // printf("Sum of list is %d", sum(&mut l2));
}
