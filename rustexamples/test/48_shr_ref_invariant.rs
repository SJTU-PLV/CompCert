struct A<'a>{
    x: &'a mut i32,
    y: &'a i32
}

fn use_shr_ref<'b>(r: &'b i32) {
    let mut tmp: i32 = *r;
}

// rustc +nightly 48_shr_ref_invariant.rs -Z polonius=next

fn main(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut v3: i32 = 3;
    let mut a: A = A {x: &mut v1, y: &v2};
    let mut p: & &i32 = &a.y; // We generate 'a = 'p2 but Polonius would generate 'a : 'p2
    a.x = &mut v3; // 'p2 contains v3 because we change 'a which also changes 'p2 since 'p2 = 'a. It is an imprecision introduced by invariant w.r.t. 'p2
    v3 = 4; // error occurs here because we restrict 'p2 is invariant of 'a. This error does not occur in Polonius becasue the subset relation ['a:'p2] is not flowed here so loan [v3] is not flowed into 'p2 at this point. But this error occurs in NLL because 'a : 'p2 is not cleared even if 'a is dead?
    use_shr_ref(*p);
    // use_shr_ref(a.y); //'a is still live here. If we uncomment this line and comment the last line, there would be error in Polonius borrow checker because loan [v3] is flowed to 'p2. However, using a.y should be irrlevant to the loan [v3]. But since we use 'a to abstract both regions of a.x and a.y, we have this imprecision here.
}