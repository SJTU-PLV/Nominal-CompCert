fn main{
    let v : i32 = 1;
    let dummy : i32 = 2;
    let dummy1 : &mut i32 = &mut dummy;
    let p : &mut i32 = &mut v;
    let x : &mut &mut i32 = &mut p; 
    let tmp : i32 = 2;
    *x = &mut tmp; 
    x = &mut dummy1;
    v = 3;
    *p = 4; 
}