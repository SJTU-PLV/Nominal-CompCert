enum S<'a, 'b> {
    x(&'a mut &'b mut i32),
    y(&'a mut i32),
}

fn main() {
    let mut v1 :i32 = 1;
    let mut p: &mut i32 = &mut v1; 
    let mut x: S = S::x(&mut p); 
    let mut dummy :i32 = 1;
    match x {
        S::x(r) => {
            let mut q: &'b mut i32 = &mut *r; 
            let mut tmp : i32 = 4;
            *q = &mut tmp; 
            tmp = 4;
            **r = 5;
        }
        S::y(_) => {
            dummy = 2;
        }
    }
}
