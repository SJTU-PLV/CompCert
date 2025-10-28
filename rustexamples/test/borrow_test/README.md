1.  Attempting to modify a borrowed value 
```
fn main() {
    let a : i32 = 2;
    let b : &i32 = &a;
    *b = 3;
}
```
2. Right mutable borrow
```
fn main() {
    let a : i32 = 2;
    let b : &mut i32 = &mut a;
    *b = 3;
}
```

3. Multiple mutable borrow
```
fn main() {
	let a : i32 = 2;
	let r1 : &mut i32 = &mut a;
	let r2 : &mut i32 = &mut a;
}
```
4. Multiple mutable borrow in different scope
```
fn main() {
	let a : i32 = 2;
	
	{
		let r1 : &mut i32 = &mut a;
	}

	let r2 : &mut i32 = &mut a;
}
```
5. combining mutable and immutable references
```
fn main() {
	let a : i32 = 2;
	let r1 : &i32 = &a;
	let r2 : &mut i32 = &mut a;
	println!("{} and {}", r1, r2);
}
```
// supposed error message
```
error[E0502]: cannot borrow `a` as mutable because it is also borrowed as immutable
```
6. combining mutable and immutable references
```
fn main() {
	let a : i32 = 2;
	let r1 : &i32 = &a;
	let r2 : &i32 = &a;
	println!("{} and {}", r1, r2);
	let r3 : &mut i32 = &mut a; 
	println!("{}", r3);
}
```
7. dangling reference
```
fn main() {

    let reference_to_nothing : &i32 = dangle();

}
fn dangle() -> &i32 {
    let a : i32 = 2;
    &a
}
```
8. no dangling reference
```
fn main() {
    let b : i32 = no_dangle();
}
fn no_dangle() -> i32 {
    let a : i32 = 2;
    a
}
```
9. classic borrow check
10. disjoint origins cannot affect each other
11. A little complicated reference to reference. An assignment to a
    dereference does not kill the lifetime of the local variable
12. Test alias graph: copy and modified from
    `assign_deref_weak_update.rs`. The key point is that *x indirectly
    changes p so that tmp and *p alias. It test the functionality of
    alias graph.
13. A normal re-borrow test
14. A test that is not compiled in NLL but can be compiled in Polonius
15. Borrow from a box and move that box
16. Test if statement
17. Test loop
18. Use after free error
19. test share reference
20. Polonius example from [https://smallcultfollowing.com/babysteps/blog/2023/09/29/polonius-part-2/]
21. Generic origin in struct and enum
22. Return dangling pointer
23. Problem case #4 from NLL RFC
24. check the functionality of function call. `assign` is similar to the `assign` function in [https://doc.rust-lang.org/nomicon/subtyping.html#variance]
25. List implemented with reference. An interesting point is that if we change `add_one` to `fn add_one<'a>(l: &'a mut list<'a>)`, this code does not compile because `l2` is borrowed until the end of println which is inferred by the lifetime `'a` of `l2`. And the lifetime of borrow expression `&mut l2` in `add_one` is also `'a`.
29. mutable borrow after move (not supported yet)
30. WRONG: An example from minimized from https://github.com/rust-lang/rust/issues/134554, which cannot be passed in Polonius and NLL but can be passed in our borrow checker. Actually, it can pass Polonius but not NLL. The example in the above url is more complicated. May be related to trait bound?
31. [untested] An example to illustrate that we do not use invariant relation to check that two region are aliased or not.
32. The running example that we use to illustrate our borrow checker
33. An example rejected by Polonius. The reason may be the time-traveling problem. To solve this problem, we should maintain flow information in the relations between regions (may be some fancy union-find structure)