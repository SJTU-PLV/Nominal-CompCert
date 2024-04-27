fn main(){
    let mut v = 1;
    let mut p = &mut v;
    let mut x = &mut p; // invariant rule? 'x2 : 'p and 'p : 'x2
    let mut tmp =2;
    *x = &mut tmp; // 'tmp : 'x2
    tmp = 3;
    *p = 4; //'tmp extends to here, so line 8 errors. If we do not have constraint 'x2:'p, we cannot conclude that 'tmp extends to here
}

fn test(){
    let mut v = 1;
    let mut p = &mut v;
    let mut x = &mut p; // invariant rule? 'x2 : 'p and 'p : 'x2
    let mut y = &mut *x; // 'x2: 'y2, 'y2: 'x2
    let mut tmp =2;
    *y = &mut tmp; // 'tmp : 'y2
    tmp = 3;
    **x = 4; // 'tmp extends to here
}