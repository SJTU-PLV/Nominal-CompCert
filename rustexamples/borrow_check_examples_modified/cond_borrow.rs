fn main(){
    let v1 :i32 = 1;
    let v2 :i32 = 2;
    let v3 :i32 = 3;
    let p :&mut i32 = &mut v1;
    let a :&mut i32 = &mut v2;
    let b :&mut i32 = &mut v3;
        
    if true {
        a = &mut *p;
    }
    else {
        b = &mut *p;
    }
    v2 = 5;
    *a = 4;
}