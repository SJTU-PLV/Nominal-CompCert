struct A {
    a: i32,
    b: i32
}

enum S<'a> {
    x(&'a mut A),
    y(&'a mut i32)
}

fn main() {
    let mut v: A = A {a: 1, b: 2};
    let mut tmp: i32 = 3;
    let mut v2: i32 = 4;
    let mut s: S = S::y(&mut v2);
    
    match s {
        S::x(r) => {
            let q: &mut i32 = &mut (*r).a;
            let p: &mut i32 = &mut (*r).b;
            *q = 3;
            *p = 4
        },
        S::y(_) => {
            tmp = 4;
        }
    };
}
