
// This program compiles error

fn main(){
    let mut a = Box::new(1);
    let mut r = &mut a;
    let p = &mut r;
    let mut b = Box::new(2);
    // *b = 3; place b here does not cause error
    *p = &mut b;
    *b = 3;
    //*a = 4;
    **r = 4;
}