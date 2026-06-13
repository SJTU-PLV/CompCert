// Source: borrowck/borrowck-no-cycle-in-exchange-heap.rs

struct Node_ {
    a: Box<Cycle>
}

enum Cycle {
    Node(Node_),
    Empty
}

fn main() {
    let mut x: Box<Cycle> = Box::new(Cycle::Node(Node_ { a: Box::new(Cycle::Empty) }));

    // Create a cycle!
    match *x {
        Cycle::Node(ref mut y) => {
            y.a = x; //~ ERROR cannot move out of
        }
        Cycle::Empty => {}
    };
}
