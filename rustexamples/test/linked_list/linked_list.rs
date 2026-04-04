struct Node {
  val: i32,
  next: Box<List>
}

enum List {
  Nil,
  Cons(Node)
}

fn iterate_until_consume(mut l: Box<List>, x: i32) {
  loop {
    match *l {
      List::Nil => {
        return;
      }
      List::Cons(node) => {
        if node.val == x {
          *l = List::Nil;
        } else {
          l = node.next;
        }
      }
    }
  }
}

fn iterate_until<'a, 'b>(mut l: &'a mut List, x: i32) -> &'b mut List
where
    'a: 'b
{
  loop {
    match *l {
      List::Nil => {
        return l;
      }
      List::Cons(ref mut node) => {                
        if (*node).val == x {
          return &mut *(*node).next;
        } else {
          l = &mut *((*node).next);
        }
      }
    }
  }
}



fn main() {
    // produce a list 10 -> 9 -> ... -> 1 -> Nil
    let mut l: Box<List> = init_list(10);

    // Iterate until 5, and print the suffix list starting from 4
    let mut l1: &mut List = iterate_until(&mut *l, 5);

    // Using l is not allowed here because l1 still borrows l
    iterate_until_consume(l, 7); 

    print_list(&*l1);

}

// init(n) produces the list n -> (n-1) -> ... -> 1 -> Nil
fn init_list(n: i32) -> Box<List> {
    if n == 0 {
        return Box::new(List::Nil);
    } else {
        return Box::new(List::Cons(Node {
            val: n,
            next: init_list(n - 1)
        }));
    }
}

// Printing functions implemented in C
extern "C" {
    fn print_i32(x: i32);
    fn print_endl();
    fn print_prompt();
}

fn print_list<'a>(l: &'a List) {
    unsafe {
        print_prompt();
    };
    print_list_rec(l);
}

fn print_list_rec<'a>(l: &'a List) {
    match *l {
        List::Nil => {
            unsafe {
                print_endl();
            }
        }
        List::Cons(ref node) => {
            unsafe {
                print_i32((*node).val);
            };
            print_list_rec(&(*(*node).next));
        }
    }
}


