enum S<'a, 'b, 'c> {
    x(&'a mut &'b mut i32),
    y(&'a mut &'c mut i32),
}

fn main() {
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut tmp: i32 = 3;
    let mut dummy: i32 = 4;
    let mut a: &mut i32 = &mut v1;
    let mut p: &mut &mut i32 = &mut a;
    let mut b: &mut i32 = &mut v2;
    let mut q: &mut &mut i32 = &mut b;
    let mut s: S;
    if true {
        s = S::x(p);
    } else {
        s = S::y(q);
    }
    match s {
        S::x(r) => {
            *r = &mut tmp; 
            tmp = 4;
            **q = 3;
            tmp = 5;
        }
        S::y(_) => {
            dummy = 4;
        }
    }
}
