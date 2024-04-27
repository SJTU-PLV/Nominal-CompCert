
struct S {
    f: Box<i32>,
    g: i32
}

// This example is a counter example for the alias model proposed in
// RustSEM paper
fn main(){
    let mut s1 = Box::new(S{f: Box::new(1), g: 2});
    let s2 = &mut *((*s1).f);
    println!("{}", (*s1).g);
    // *s1 = Box::new(1);
    //test(&mut (*s1));
    println!("{}", *s2);
}

// the following code compile error
// fn main(){
//     let mut s1 = Box::new(Box::new(2));
//     let s2 = &mut **s1;
//     //println!("{:?}", *s1);
//     *s1 = Box::new(1); // any code that uses *s1
//     println!("{}", *s2);
// }