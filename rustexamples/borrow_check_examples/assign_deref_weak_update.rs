fn main{
    let mut v = 1;
    let mut dummy = 2;
    let mut dummy1 = &mut dummy;
    let mut p = &mut v;
    let mut x = &mut p; // invariant rule? 'x2 : 'p and 'p : 'x2
    let mut tmp =2;
    *x = &mut tmp; // 'tmp : 'x2, now p points to tmp and v?
    x = &mut dummy1;// kills 'x2
    v = 3;
    *p = 4; // but 'p2 extends 'x2 to here
}