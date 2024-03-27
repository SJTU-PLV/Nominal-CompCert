1.  Attempting to modify a borrowed value (crashed)
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

3. Multiple mutable borrow (crashed)
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
5. combining mutable and immutable references(crashed)
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
7. dangling reference(crashed)
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