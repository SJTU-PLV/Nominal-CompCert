fn main(){
    let mut v : i32 = 1;
    let mut p : &mut i32 = &mut v;
    let mut x : &mut &mut i32 = &mut p; 
    let mut tmp : i32 = 2;
    *x = &mut tmp; 
    tmp = 3;
    *p = 4; 
}

fn test(){
    let mut v : i32 = 1;
    let mut p : &mut i32 = &mut v;
    let mut x : &mut &mut i32 = &mut p; 
    let mut y : &mut &mut i32 = &mut *x; 
    let mut tmp : i32 = 2;
    *y = &mut tmp; 
    tmp = 3;
    **x = 4; 
}