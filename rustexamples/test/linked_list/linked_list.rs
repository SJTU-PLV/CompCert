enum List;
struct Node;

struct Node {
    val: i32,
    next: Box<List>
}

enum List {
    Nil,
    Cons(Node)
}

fn iterate_until<'a, 'b>(mut l: &'a mut List, x: i32) -> &'b mut List
    where 'a: 'b
{
    loop {
        match *l {
            List::Nil => {
                return l;
            }
            List::Cons(ref mut node) => {
                // node: &mut Node = &mut (*l as Cons)
                l = &mut *((*node).next);
                if (*node).val == x {
                    return l;
                }
            }
        }
    }
}

fn iterate_until_consume(l: Box<List>, x: i32) {
    match *l {
        List::Nil => {
            return;
        }
        List::Cons(node) => {
            if node.val != x {
                l = node.next;
                iterate_until_consume(l, x);
            }
        }
    }
}

// init(3) produces the list 3 -> 2 -> 1 -> Nil
fn init_list(n: i32) -> Box<List> {
    if n == 0 {
        return Box::new(List::Nil);
    } else {
        return Box::new(List::Cons(Node { val: n, next: init_list(n - 1) }));
    }
}

fn main() {
    let mut l: Box<List> = init_list(100);
    // let mut l1: &mut List = iterate_until(&mut *l, 90);
    iterate_until_consume(l, 90);
    // print_list(& *l1);
}


// Printing functions implemented in C
extern fn print_i32(x: i32)
extern fn print_endl()

fn print_list<'a>(l: &'a List) {
    match *l {
        List::Nil => {
            print_endl();
        }
        List::Cons(ref node) => {
            print_i32((*node).val);
            print_list(&(*(*node).next));
        }
    }
}