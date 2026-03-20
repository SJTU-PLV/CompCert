struct Node{
    val: i32;
    link: Link;
}

extern Link {size: 16; align: 16}

extern fn empty_link() -> Link;

extern fn push_front(Box<Data> l, Box<Data> n) -> Box<Data>;

fn link_offset() -> u64{
    return 16;
}

fn create(v: i32) -> Box<Node> {
    // We can call an assembly program to encrypt the value and then store it to the list. The pop functions can decrypt the value.
    let head : Box<Node> = Box::new(Node{val: v, link: empty_link()});
    return create_link(head);
}

fn push(l: Box<Node>, v: i32) -> Box<Node> {
    let head: Box<Node> = Box::new(Node {val: v, link: empty_link()});
    l = push_front(l, head);
    return l;
}

struct Option{
    None,
    Some(i32, Box<Node>)
}