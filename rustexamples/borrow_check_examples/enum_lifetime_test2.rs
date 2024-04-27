struct A{
    a: i32,
    b: i32
}

enum S<'a>{
    x(&'a mut A),
    y(&'a mut i32)
}

fn main(){
    let mut v = A{a: 1, b: 2};
    // let v1 = &mut v;
    // let p = &mut (*v1).a;
    // let q = &mut (*v1).b;
    // *p = 2;
    // *q = 3; // no error
    
    let mut tmp = 3;
    let mut v2 = 4;
    let mut s = S::y(&mut v2);
    match s {
        S::x(r)=>{
            // r and v2 alias, how to represent it in the abstract memory?
            let q = &mut (*r).a;
            let p = &mut (*r).b;
            *q = 3;
            // v2 = 5; // error
            *p = 4
        },
        S::y(_) =>
            tmp = 4
    };
}