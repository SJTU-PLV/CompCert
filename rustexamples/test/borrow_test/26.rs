enum S<'a, 'b> {
    s1(&'a mut &'b mut i32),
    s2(&'a mut i32)
}

fn main() {
    let v1 :i32 = 1;
    let p: &mut i32 = &mut v1; 
    let x: S = S::s1(&mut p); 
    let dummy : i32 = 1;
    match x {
        S::s1(r) => {
            let q: &mut &mut i32 = &mut *r; 
            let tmp : i32 = 4;
            *q = &mut tmp; 
            tmp = 4;
            // **r = 5; if uncomment this line, last line would be an error usage of tmp
        }
        S::s2(r1) => {
            dummy = 2;
        }
    }
}