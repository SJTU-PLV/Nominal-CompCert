struct B{
    l: Box<i32>,
    m: i32,
    n: i32
}

struct A{
    f: Box<B>,
    g: i32,
    h: Box<i32>
}

fn main(){
    let mut a : A= A{f: Box(B{l: Box(1), m: 2, n: 3}), g: 4, h: Box(5)};
    let b : Box<i32> = a.f.l;
    a.f.l = b;
}