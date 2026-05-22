// A modified version of the code in Problem#3 of https://rust-lang.github.io/rfcs/2094-nll.html#problem-case-3-conditional-control-flow-across-functions

struct Node {
    value: i32,
    next: Box<List>
}

enum List {
    Nil,
    Cons(Node)
}

enum OptionR<'b> {
    None,
    Some(&'b mut i32)
}

// The implementation is irrelevant; Since we do not support returning
// struct/enum directly, we use an output parameter to return the
// result. The region of this output parameter should be different
// from the region of list otherwise the borrow checker would report
// error in match
fn get_mut<'a, 'b, 'c>(list: &'a mut List, key: i32, ret: &'c mut OptionR<'b>) where 'a: 'b{
    match *list {
        List::Cons(ref mut node) => {
            *ret = OptionR::Some(&mut (*node).value);
        }
        List::Nil => {
            *ret = OptionR::None;
        }
    }
}

fn insert_into_list<'a>(list: &'a mut List, key: i32, v: i32) {
    *list = List::Cons(Node { value: v, next: Box::new(List::Nil) });
}

fn get_default<'r>(list: &'r mut List, key: i32, default: &'r mut i32) -> &'r mut i32 {
    let mut opt_node: OptionR = OptionR::None;
    get_mut(&mut *list, key, &mut opt_node);
    match opt_node{
        OptionR::Some(v) => {
            return v;
        }
        OptionR::None => {
            insert_into_list(&mut *list, key, *default);
            // In NLL, this is considered an error because *list is considered be borrowed at the Cons branch and this borrow fact is propagated to this branch due to flow-insensitivity of NLL.
            return default;
        }
    }
}

fn main(){}