// test cond branch
fn main(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut v4 = 4;
    let mut p = &mut v1; // p: {&mut v1}
    let mut q = &mut v2; // q: {&mut v2}
    let mut a = &mut v3;
    let mut b = &mut v4;
    
    let mut l = 11;
    
    if true {
        p = &mut l; // p: {&mut v1, &mut l}
    }
    else {
        q = &mut l; // q: {&mut v2, &mut l}
    }
        

    if true {
        a = &mut *p; // a: {&mut v1, &mut l, &mut *p}
    }
    else {
        b = &mut *q; // b: {&mut v2, &mut l, &mut *q}
    }
    
    // use q and a
    *q = 4; // invalidate [&mut *q], so b is unusable
    *a = 3; // no problem!
    
}

// test kill some tag in one branch
fn test1(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut v4 = 4;
    let mut p = &mut v1;
    let mut q = &mut v2;
    let mut a = &mut v3;
    let mut b = &mut v4;
    
    let q = &mut *p; // v1 : [p;q]
    
    if true {
        a = &mut *q; // v1 : [p;q;a]
    }
    else{
        *p = 5; //v1 : [p]
    }
    
    // borrow stack of v1 ?
    
    // *q = 4; // error
    // *a = 4;
}

fn test2(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut v4 = 4;
    let mut v5 = 5;
    let mut p = &mut v1;
    let mut q = &mut v2;
    let mut a = &mut v3;
    let mut b = &mut v4;
    let mut c = &mut v5;
    
    let q = &mut *p; // v1 : [p;q]
    
    if true {
        a = &mut *q; // v1 : [p;q;a]
    }
    else{
        *p = 5; //v1 : [p]
        c = &mut *p; // v1 : [p;c]   
    }
    
    // borrow stack of v1 ?
    
    // *q = 4; // error
    // *a = 4;
    *c = 4;
}

fn test3(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut v4 = 4;
    let mut v5 = 5;
    let mut p = &mut v1;
    let mut q = &mut v2;
    let mut a = &mut v3;
    let mut b = &mut v4;
    let mut c = &mut v5;
    
    if true {
        a = &mut *p; // v1 : [p;a]
    }
    else{
        if true {
            b = &mut *p;
        }
        else {
            c = &mut *p;
        }
    }
    
    // borrow stack of v1 ?
    
    *c = 4;
}