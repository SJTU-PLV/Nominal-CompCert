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
    let a : A = A {
        f: Box(Box(
            B{ l: Box(1), 
               m: Box(2), 
               n: 3})), 
        g: Box(4), 
        h: 5
    };
    let b : Box<i32> = (**(a.f)).l;

    printf("Success\n");
}