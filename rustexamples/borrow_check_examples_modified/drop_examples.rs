fn main() {
    
    let a : i32 = Box::new(12);
    loop {
        if t() {
            a = Box::new(13); 
        }
        else { 
            a = Box::new(3); 
            let b : i32 = a;
        }
    }

}

fn t() -> bool {
    return false;
}