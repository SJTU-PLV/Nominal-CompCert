fn main(){
    let v: i32 = 1;
    let p: &mut i32 = &mut v;
    let q: &mut &mut i32 = &mut p;
    v = 2;
    let v1: i32 = 3;
    *q = &mut v1;
}