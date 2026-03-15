enum list;
struct list_node;

struct list_node {
    value : i32,
    next : Box<list>
}

enum list {
    nil,
    cons(list_node)
}

// It pops an element from a list and then pushes [v] in the list
fn pop_and_push(l: Box<list>, v: i32) -> Box<list> {
    let head : list_node;
    head.value = v;
    match *l {
        list::nil => {      
            head.next = Box(list::nil);
        } 
        list::cons(tl) => {
            head.next = tl.next;
        }
    };
    let ret : list = list::cons(head);
    return Box(ret);
}

fn push(l: Box<list>, v: i32) -> Box<list> {
    let head : list_node = list_node {value: v, next: l};
    return Box(list::cons(head));
}

fn print_list(l: Box<list>) {
    match *l {
        list::nil => {      
            return;
        } 
        list::cons(tl) => {
            printf("%d, ", tl.value);
            print_list(tl.next);
        }
    };
}

fn main(){
    let head : list_node;
    head.value = 0;
    head.next = Box(list::nil);
    let ls : Box<list> = Box(list::cons(head));
    ls = push(ls, 1);
    ls = push(ls, 2);
    ls = push(ls, 3);
    let l1 : Box<list> = pop_and_push(ls, 4);
    // result is 4 2 1 0  
    printf("The elements of list is: ");
    print_list(l1);
}
