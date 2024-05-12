fn main(){
    let v : i32 = 1;
    let p : &mut i32 = &mut v;
    let x : &mut &mut i32 = &mut p; 

    let tmp : i32 = 2;

    *x = &mut tmp;
    v = 3;
    **x = 1; 
}
