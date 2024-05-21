enum list<'a, 'b>{
    nil(),
    cons(i32, &'a mut list<'a, 'b>)
}


fn test(){
    let mut v :i32 = 3;
    let q: &mut i32;
    {
        let p = &mut v;
        q = &mut *p;
    }
    *q = 4;
}

enum S<'a, 'b>{
    x(&'a mut i32),
    y(&'a mut &'b mut i32)
}

fn test_s<'a,'b>(mut s: S<'a,'b>){
    let mut v :i32 = 1;
    let mut tmp :i32 =3;
    let mut p :&mut i32= &mut v;
    match &mut s {
        // unsupported binding
        S::x(ref mut q) => {
            p = &mut **q;
        }
           
        S::y(_) => {
            tmp = 3
        }
    };
    match &mut s {
        S::x(ref mut q) => {
            **q = 5;
        }
            
        S::y(_) => {
            tmp = 3;
        }
    };
    *p = 4;
}

enum S<'a, 'b>{
    x(&'a mut i32),
    y(&'a mut i32),
    z(&'b mut i32)
}

fn main(){
    let mut v :i32 = 1;
    let mut tmp :i32 = 2;
    let mut s = S::x(&mut v);
    match s {
        S::x(_) => {
            tmp = 3;
        }
        S::y(r) => {   
            v = 2; 
            *r = 3;
        }
        S::z(_) => {
            tmp = 3;
        }
    };
}