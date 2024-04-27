// N.B. the following code compiles in Polonius but fails in NLL
// rustc +nightly -Zpolonius nll_test1.rs 

fn main(){
    let mut v = 1;
    let mut tmp = 2;
    let mut p = &mut v;// v \in 'p
    let mut q = &mut *p; // 'p: 'q
    p = &mut tmp; // 'tmp : 'p, nll does not consider that 'p is killed here
    *q = 5; // 'q extends to here, so that 'p is extends to here
    v = 4;
    *p = 3; // 'q (stage 2) extends to here, so 'p = {l5, l6, l7, l8, l9}. We cannot use v in l8
    // But what we want is that 'p = {l5, l7, l8, l9} and 'v = {l5, l6 , l7} because 'v : 'q
}