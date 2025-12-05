
fn read_non_empty<'c>(x: &'c mut i32) -> &'c mut i32
{
    // 'c: {'c} 
    // loop {
    //     let b = &mut *x; // although mutable reference of *x would invalid 'b, reassigning b would make it valid again; 'b: {*x, 'c}
    //     if *b > 3 {
    //         return b; // 'c : {'c, *x}
    //     } // 'c: {'c}
    // }

    
    // let b = &mut *x; // although mutable reference of *x would invalid 'b, reassigning b would make it valid again; 'b: {*x, 'c}
    // if *b > 3 {
    //     return b; // 'c : {'c, *x}
    // } // 'c: {'c}
    
    // b = &mut *x; // although mutable reference of *x would invalid 'b, reassigning b would make it valid again; 'b: {*x, 'c}
    // if *b > 3 {
    //     return b; // 'c : {'c, *x}
    // } // 'c: {'c}
    // return b;

    let b: &mut i32 = &mut *x; // although mutable reference of *x would invalid 'b, reassigning b would make it valid again; 'b: {*x, 'c}
    if *b > 3 {
        return b; // 'c : {'c, *x}
    } // 'c: {'c}
    
    b = &mut *x; // although mutable reference of *x would invalid 'b, reassigning b would make it valid again; 'b: {*x, 'c}
    if *b > 3 {
        return b; // 'c : {'c, *x}
    } // 'c: {'c}
    return b;
}

//rustc +nightly 30.rs -Z dump-mir=all -Z polonius=next

fn main(){
} 
