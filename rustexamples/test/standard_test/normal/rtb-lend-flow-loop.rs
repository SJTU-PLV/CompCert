// Source: borrowck/borrowck-lend-flow-loop.rs

fn borrow(_v: &i32) {}
fn borrow_mut(_v: &mut i32) {}
fn cond() -> bool { return false; }

fn inc(v: &mut Box<i32>) {
    *v = Box::new(**v + 1);
}

fn loop_overarching_alias_mut() {
    let mut v1: Box<i32> = Box::new(3);
    let mut x1: &mut Box<i32> = &mut v1;
    **x1 = **x1 + 1;
    loop {
        borrow(&*v1);
    }
}

fn block_overarching_alias_mut() {
    let mut v2: Box<i32> = Box::new(3);
    let mut x2: &mut Box<i32> = &mut v2;
    let mut i: i32 = 0;
    while i < 3 {
        borrow(&*v2); //~ ERROR cannot borrow
        i = i + 1;
    }
    *x2 = Box::new(5);
}

fn loop_aliased_mut() {
    let mut v3: Box<i32> = Box::new(3);
    let mut w3: Box<i32> = Box::new(4);
    let mut x3: &Box<i32> = &w3;
    loop {
        borrow_mut(&mut *v3);
        x3 = &v3;
    }
}

fn while_aliased_mut() {
    let mut v4: Box<i32> = Box::new(3);
    let mut w4: Box<i32> = Box::new(4);
    let mut x4: &Box<i32> = &w4;
    while cond() {
        borrow_mut(&mut *v4);
        x4 = &v4;
    }
}

fn loop_aliased_mut_break() {
    let mut v5: Box<i32> = Box::new(3);
    let mut w5: Box<i32> = Box::new(4);
    let mut x5: &Box<i32> = &w5;
    loop {
        borrow_mut(&mut *v5);
        x5 = &v5;
        break;
    }
    borrow_mut(&mut *v5);
}

fn while_aliased_mut_break() {
    let mut v6: Box<i32> = Box::new(3);
    let mut w6: Box<i32> = Box::new(4);
    let mut x6: &Box<i32> = &w6;
    while cond() {
        borrow_mut(&mut *v6);
        x6 = &v6;
        break;
    }
    borrow_mut(&mut *v6);
}

fn while_aliased_mut_cond(cond: bool, cond2: bool) {
    let mut v7: Box<i32> = Box::new(3);
    let mut w7: Box<i32> = Box::new(4);
    let mut x7: &mut Box<i32> = &mut w7;
    while (cond) {
        **x7 = **x7 + 1;
        borrow(&*v7); //~ ERROR cannot borrow
        if cond2 {
            x7 = &mut v7;
        }
    }
}

fn main() {
    loop_overarching_alias_mut();
    block_overarching_alias_mut();
    loop_aliased_mut();
    while_aliased_mut();
    loop_aliased_mut_break();
    while_aliased_mut_break();
    while_aliased_mut_cond(true, false);
}
