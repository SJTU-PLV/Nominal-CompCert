enum S<'a, 'b> {
    x(&'a mut &'b mut i32),
    y(&'a mut i32)
}

fn main() {
    let v1 :i32 = 1;
    let p: &mut i32 = &mut v1; 
    let x: S = S::x(&mut p); 
    let dummy : i32 = 1;
    match x {
        S::x(r) => {
            let q: &mut &mut i32 = &mut *r; 
            let tmp : i32 = 4;
            *q = &mut tmp; 
            tmp = 4;
            **r = 5;
        }
        S::y(r1) => {
            dummy = 2;
        }
    }
}