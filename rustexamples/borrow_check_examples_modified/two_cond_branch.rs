fn main(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut v3: i32 = 3;
    let mut v4: i32 = 4;
    let mut p: &mut i32 = &mut v1; 
    let mut q: &mut i32 = &mut v2; 
    let mut a: &mut i32 = &mut v3;
    let mut b: &mut i32 = &mut v4;
    
    let mut l: i32 = 11;
    
    if true {
        p = &mut l; 
    }
    else {
        q = &mut l; 
    }
        

    if true {
        a = &mut *p; 
    }
    else {
        b = &mut *q; 
    }
    
    *q = 4; 
    *a = 3; 

fn test1(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut v3: i32 = 3;
    let mut v4: i32 = 4;
    let mut p: &mut i32 = &mut v1;
    let mut q: &mut i32 = &mut v2;
    let mut a: &mut i32 = &mut v3;
    let mut b: &mut i32 = &mut v4;
    
    let q: &mut i32 = &mut *p; 
    
    if true {
        a = &mut *q; 
    }
    else{
        *p = 5; 
    }
    
}

fn test2(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut v3: i32 = 3;
    let mut v4: i32 = 4;
    let mut v5: i32 = 5;
    let mut p: &mut i32 = &mut v1;
    let mut q: &mut i32 = &mut v2;
    let mut a: &mut i32 = &mut v3;
    let mut b: &mut i32 = &mut v4;
    let mut c: &mut i32 = &mut v5;
    
    let q: &mut i32 = &mut *p; 
    
    if true {
        a = &mut *q; 
    }
    else{
        *p = 5; 
        c = &mut *p;  
    }
    
    *c = 4;
}

fn test3(){
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let mut v3: i32 = 3;
    let mut v4: i32 = 4;
    let mut v5: i32 = 5;
    let mut p: &mut i32 = &mut v1;
    let mut q: &mut i32 = &mut v2;
    let mut a: &mut i32 = &mut v3;
    let mut b: &mut i32 = &mut v4;
    let mut c: &mut i32 = &mut v5;
    
    if true {
        a = &mut *p; 
    }
    else{
        if true {
            b = &mut *p;
        }
        else {
            c = &mut *p;
        }
    }
    *c = 4;
}