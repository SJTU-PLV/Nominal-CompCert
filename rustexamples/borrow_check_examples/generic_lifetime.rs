struct List {
    data: u32,
    next: Option<Box<List>>
}

struct S<'s>{
    v: u32,
    p: &'s u32
}


struct S1<'s>{
    v: u32,
    p: &'s mut u32
}


fn print_all(mut p: &mut List) {
    loop {
        println!("{}", p.data);
        if let Some(n) = &mut p.next {
            p = n;
        } else {
            break;
        }
    }
}

fn max_ref<'c, 'a : 'c, 'b: 'c>(a: & 'a mut i32, b: & 'b mut i32) -> & 'c mut i32 {
    if *a > *b {
        return a
    }
    else {
        return b
    }
}

fn max_ref1<'a>(a: & 'a mut i32, b: & 'a mut i32) -> & 'a mut i32 {
    let p = &mut *a;
    *b = 5;
    *p = 4;

    if *a > *b {
        return a
    }
    else {
        return b
    }
}

// error 
// fn max_ref2<'c, 'a ,'b>(a: & 'a mut i32, b: & 'b mut i32) -> & 'c mut i32 {
//     if *a > *b {
//         return a
//     }
//     else {
//         return b
//     }
// }


fn two_ref_andS<'a,'b,'c>(a: &'a u32, b:&'b u32, c: S<'c>){
    
}

fn main(){
    let v = 12;
    let p1 = & v;
    let p2 = & v;
    let s = S{v:3, p: &v};
    two_ref_andS(p1, p2 ,s);
    
    
}

