//                                a
//                a.f             a.g            a.h 
//               *a.f
//              **a.f
//     **a.f.l  **a.f.m  **a.f.n
// move **a.f.l, what would be dropped?


struct B{
    l: Box<i32>,
    m: Box<i32>,
    n: i32
}

struct A{
    f: Box<Box<B>>,
    g: Box<i32>,
    h: i32
}

fn main(){
    let a = A{f: Box::new(Box::new(B{ l:Box::new(1), m: Box::new(2), n: 3})), g: Box::new(4), h: 5};
    let b = (**(a.f)).l;

    // inserted drops:
    
    // drop(b);

    // drop((**(a.f)).m);
    // drop(*(a.f));
    // drop(a.f);
    // drop(a.g);
}