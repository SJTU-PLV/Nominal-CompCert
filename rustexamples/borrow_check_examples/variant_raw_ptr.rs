enum list{
    nil,
    cons(* mut i32)
}

fn main(){
    let mut v = 12;
    let p = &mut v;
    let l1 = list::cons(p as *mut i32);
    v = 13;
    match l1 {
        list::nil => println!("No"),
        list::cons(r) => unsafe {*r = 14} // miri check error
    }

}

// struct S<'a>{
//     f: i32,
//     g: &'a mut i32
// }

// struct S1{
//     f: i32,
//     g: *mut i32
// }

// fn main(){
//     let mut v = 12;
//     let p = &mut v;
//     // let s = S1 {f: 1, g: p as *mut i32};
//     let s = S {f: 1, g: p };
//     v = 13;
//     // println!("{}", unsafe { *(s.g) });
//     println!("{}", s.f);
// }

