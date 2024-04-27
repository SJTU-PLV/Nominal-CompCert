fn main(){
    let mut v = 1;
    let mut p = &mut v; // 'v : 'p
    let mut x = &mut p; // 'x2 : 'p, 'p : 'x2
    // let mut y = &mut *x;
    let mut tmp =2;
    // if we change *x =... to x = ..., the following code compiles
    *x = &mut tmp;// assign *x does not kill the lifetime of *x, 'tmp:'x2
    // if assign to *x kills 'x2, p is just extended to line 5, so is v, but in NLL, 'x2 is bind to x instead of *x
    //*y = &mut tmp;
    // println!("{}", **x);
    v = 3;
    // *p = 4;// error, but *p and v do not alias
    **x = 1; // error, but **x and v do not alias, 'v extends to here because of ('v: 'p: 'x2)
    // **y = 3;
}
