fn main(){
    // let mut v = 1;
    // let mut p = &mut v;
    // let mut q = &mut p;
    // let mut x = &mut *q;
    // let mut y = &mut **q;
    // **x; // borrow checker error 
    
    unsafe {
    let mut v = 1_i32;
    let mut p = &mut v as *mut i32;
    let mut q = &mut p as *mut *mut i32;
    let mut x = &mut *q as *mut *mut i32;
    let mut y = &mut **q;
    **x = 3; 
    let v2 = *y; // stacked borrow error! because we pop the tag of y in [**x=3]    
    // test the tag of x is poped or not in p

    // in fact ,no error. So deference a place is considered a read
    // access of this place and we do not consider how we use this
    // dereference (e.g., mutable reference or others)

    // let mut v1 = 2_i32;
    // *x = &mut v1 as *mut i32;
    
    }
}