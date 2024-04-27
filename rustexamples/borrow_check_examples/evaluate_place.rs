
// When creating mutable reference &mut p, the evaluation of p is
// write access for all the prefixes of p. But I cannot understand the
// reason for this.
fn main(){
    let mut v = 1;
    let mut b = &mut v;
    let a = &mut b;
    let d = &mut *a;
    let c = &mut **a; // invalidate d or not?
    //use d
    let x = d; //error!
    
}