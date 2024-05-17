fn main(){
    let v: i32 = 1;
    let tmp: i32 = 2;
    let p: &mut i32 = &mut v;
    let q: &mut i32 = &mut *p;
    p = &mut tmp;
    *q = 5;
    v = 4;
    *p = 3;
}