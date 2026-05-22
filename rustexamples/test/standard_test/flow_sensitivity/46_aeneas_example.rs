// An example coming from the thesis "Formal Verification of Rust
// programs by functional translation", which demonstrates the
// imprecision of NLL. It can be checked by our borrow
// checker and rustc's Polonius.

struct Node {
    value: i32,
    next: Box<List>
}

enum List {
    Nil,
    Cons(Node)
}

fn get_suffix_at_x<'a>(ls: &'a mut List, x: i32) -> &'a mut List {
    match *ls {
       List::Nil => { 
           return ls;
       }
       List::Cons(ref mut node) => { 
           let mut hd: &mut i32 = &mut (*node).value;
           let mut tl: &mut List = &mut *(*node).next;
           if *hd == x { 
               return ls;
           } else {
               return get_suffix_at_x(tl, x);
           }
       }
    }
}

fn main() {}
