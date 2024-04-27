// test cond branch
fn main(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut p = &mut v1;
    let mut a = &mut v2;
    let mut b = &mut v3;
        
    if true {
        a = &mut *p;
    }
    else {
        b = &mut *p;
    }
    v2 = 5;
    *a = 4;
    
}