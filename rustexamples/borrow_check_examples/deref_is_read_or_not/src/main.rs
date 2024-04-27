// This code has no UB in Tree-borrow!!! Because the read of *q is a
// foreign read, it just frozen the tag of x, but we still can read
// *x!! So we cannot use this method to design our borrow checker!
// MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri run

//It is UB in stacked-borrow because the read of *q would pop the tag of x

fn main(){
    unsafe {
    let mut v = 1_i32;
    let mut p = &mut v as *mut i32;
    let mut q = &mut p as *mut *mut i32;
    let mut x = &mut *q as &mut *mut i32;
    // use q and x to modify v
    **q = 3;
    **x = 4;
    
    }
}