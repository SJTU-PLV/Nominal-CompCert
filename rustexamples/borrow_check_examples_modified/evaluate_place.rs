fn main(){
    let mut v : i32 = 1;
    let mut b : &mut i32 = &mut v;
    let a : &mut i32 = &mut b;
    let d : &mut i32 = &mut *a;
    let c : &mut i32 = &mut **a; 
    let x : &mut i32 = d; 
    
}