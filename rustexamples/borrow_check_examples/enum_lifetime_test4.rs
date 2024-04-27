enum S<'a, 'b, 'c>{
    x(&'a mut &'b mut i32),
    y(&'a mut &'c mut i32)
}


fn main(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut tmp = 3;
    let mut dummy = 4;
    let mut a = &mut v1;
    let mut p = &mut a;
    let mut b = &mut v2;
    let mut q = &mut b;
    let mut s: S;
    if true{
        s = S::x(p);
    }
    else{
        s = S::y(q);
    }
    match s{
        S::x(r)=>{
            // **q = 2; //cannot assign to `**q` because it is borrowed
            // **r = 3 
            *r = &mut tmp; // 'tmp : 'b, although r may alias with q, *r has no relation with *q
            tmp = 4;
            **q = 3;
            tmp = 5
            
        },
        S::y(_)=>{
            dummy = 4
        }
    }
    
}