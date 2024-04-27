
enum list<'a> {
    nil,
    // cons(i32, &'a mut list<'a>)
    cons(i32, &'a list<'a>)
}

// impl<'a> Drop for list<'a>{
//     fn drop(&mut self){
//         println!("Drop list");
//     }
// }

fn list_length<'a>(mut l : & list<'a>) -> i32 {
    let mut len = 0;
    loop {
        match *l {
            list::nil => return len,
            list::cons(v, next) =>
                { len = len + v;
                  l = next }
        };
    }
}

fn main(){
    let mut l0 = list::nil;
    
    // let mut l1 = &mut l0;
    let mut l1 = list::cons(1, & l0);
    let mut v = 1;
    //use l0
    let l2 = l0;
    
    // error: because l1 is considered be used
    match l1 {
        list::nil => v = 2,
        list::cons(val, _ ) => v = val,
    };

}


enum list<'a> {
    nil,
    // cons(i32, &'a mut list<'a>)
    cons(i32, &'a  list<'a>)
}


// impl<'a> Drop for list<'a>{
//     fn drop(&mut self){
//         println!("Drop list");
//     }
// }

// fn list_length<'a>(mut l : & list<'a>) -> i32 {
//     let mut len = 0;
//     loop {
//         match *l {
//             list::nil => return len,
//             list::cons(v, next) =>
//                 { len = len + 1;
//                   l = next }
//         };
//     }
// }

// a: b1, aptr , *a : b2, scalar
// b: b3, aptr,t1 , *b : b4, scalar c : aptr,t1 *c: b5, scalar
// l: b5, Venum({nil, cons(scalar, aptr =(b6, path, tag))}),  
// b6: set of blocks
// b, c -> (r1: set of blocks)

// if *b == *c {
    
// }


// fn test(a: Box<i32>, b: & i32, c: & i32, l: list<'a>){
//     match l {
//         nil =>
//         cons(v, l') =>
//     }
// }

fn test(a: Box<i32>, b: &i32){
    
}
fn test2(){

    // let v = Box::new(1);
    // let p = &*v;
    // test(v, p);

    let mut l0 = list::nil;

    // let mut l1 = &mut l0;
    let mut l1 = list::cons(1, & l0); // l1 : 1 - l0
    let mut v = 1;
    //use l0
    let l2 = l0;
    
    // error: because l1 is considered be used
    match l1 {
        list::nil => v = 2,
        list::cons(val, _ ) => v = val,
    };
    
}