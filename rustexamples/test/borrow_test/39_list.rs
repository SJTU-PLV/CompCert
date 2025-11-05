// I have no idea is it necessary to give such a compilcated example

enum List<'r>;

struct Node<'r>;

struct Node<'r> {
    val : &'r mut i32,
    next : &'r mut List<'r>
}

enum List<'r> {
    Nil,
    Cons(Node<'r>)
}


fn reborrow_head<'a, 'b, 'c, 'd>(l: &'a mut List<'b>, p1: &'c mut i32, p2: &'d mut i32) 
    where 'c: 'b, 'd: 'b {
    match *l {
        List::Nil => { return; }
        List::Cons(ref mut node) => {
            if *p1 > *p2 {
                (*node).val = &mut *p1;
            } else {
                (*node).val = &mut *p2;
            }
        }
    }
}

// This example is too compilcated and may be not very useful
// fn choose<'a, 'b, 'c, 'd, 'e>(l: &'a mut List<'b, 'c>, p1: &'d mut i32, p2: &'e mut i32) 
//     where 'd: 'b, 'e: 'b {
//     let current: &mut List = &mut *l;
//     loop{
//         match *current {
//             List::Nil => { 
//                 return;
//             }
//             List::Cons(ref mut node) => {
//                 if *node.val > 10 {
//                     if true {
//                         node.val = p1;
//                     } else {
//                         node.val = p2;
//                     }
//                     return;
//                 } else {
//                     current = &mut *(*node).next;
//                 }
//             }
//         }
//     }
// }

fn read_list_head<'a, 'b>(l: &'a List<'b>) -> i32 {
    match *l {
        List::Nil => {
            return 0;
        }
        List::Cons(ref node) => {
            return *node.val;
        }
    }
}

fn main(){
    let v1: i32 = 1; let v2: i32 = 2;
    let l0: List = List::Nil;
    let l1: List = List::Cons(Node {val: &mut v1, next: &mut l0});
    let l2: List = List::Cons(Node {val: &mut v2, next: &mut l1});
    let v3: i32 = 3; let v4: i32 = 4;
    reborrow_head(&mut l2, &mut v3, &mut v4);
    v4 = 4; // error should be reported here
    read_list_head(&l2);
}