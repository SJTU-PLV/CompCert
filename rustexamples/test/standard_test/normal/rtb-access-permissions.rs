// Repo: rust-lang/rust
// Source: borrowck/borrowck-access-permissions.rs
// E0596: cannot borrow as mutable through various access paths

struct Foo<'a> {
    f: &'a mut i32,
    g: &'a i32
}

fn main() {
    let x: i32 = 1;
    let mut x_mut: i32 = 1;

    {
        // borrow of local
        let _y1: &mut i32 = &mut x; //~ ERROR [E0596]
        let _y2: &mut i32 = &mut x_mut; // No error
    }

    {
        // borrow of deref to box
        let box_x: Box<i32> = Box::new(1);
        let mut box_x_mut: Box<i32> = Box::new(1);

        let _y3: &mut i32 = &mut *box_x; //~ ERROR [E0596]
        let _y4: &mut i32 = &mut *box_x_mut; // No error
    }

    {
        // borrow of deref to reference
        let ref_x: &i32 = &x;
        let ref_x_mut: &mut i32 = &mut x_mut;

        let _y5: &mut i32 = &mut *ref_x; //~ ERROR [E0596]
        let _y6: &mut i32 = &mut *ref_x_mut; // No error
    }

    {
        // borrowing mutably through an immutable reference
        let mut foo: Foo = Foo { f: &mut x_mut, g: &x };
        let foo_ref: &Foo = &foo;
        let _y7: &mut i32 = &mut *foo_ref.f; //~ ERROR E0596
    }
}
