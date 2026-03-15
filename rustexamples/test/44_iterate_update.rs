// This example is adapted from https://github.com/rust-lang/rust/blob/main/tests/ui/nll/polonius/iterating-updating-cursor-issue-57165.rs, which is a test for the linked-list cursor-like pattern of #46859/#48001, where the polonius alpha analysis shows the same imprecision as NLLs, unlike the datalog implementation. 

struct X;
enum OptionX;

enum OptionX {
    None,
    Some(Box<X>)
}

struct X {
    next: OptionX
}

// Both "no_control_flow" and "conditional" can pass our borrow checking. We do not have the imprecision problem in Polonius alpha (although it is not a theretical problem). 

fn no_control_flow() {
    let b: OptionX = OptionX::Some(Box(X { next: OptionX::None }));
    let p: &mut OptionX = &mut b;
    loop {
        match *p {
            OptionX::None => {
                break;
            }
            OptionX::Some(ref mut now) => {
                p = &mut (**now).next;
                // At this point, loan(*p) is killed
            }
        }
    }
}

fn conditional() {
    let b: OptionX = OptionX::Some(Box(X { next: OptionX::None }));
    let p: &mut OptionX = &mut b;
    loop {
        match *p {
            OptionX::None => {
                break;
            }
            OptionX::Some(ref mut now) => {
                if true {
                    p = &mut (**now).next;
                }
                // At this point, loan(*p) is not killed because the else branch does not kill it.
            }
        }
    }
}

fn consume_list() {
    let p: OptionX = OptionX::Some(Box(X { next: OptionX::None }));

    loop {
        match p {
            OptionX::None => {
                break;
            }
            OptionX::Some(boxed_node) => {
                if true {
                    p = (*boxed_node).next;
                } else {
                    p = OptionX::None;
                }
            }
        }
    }
}
