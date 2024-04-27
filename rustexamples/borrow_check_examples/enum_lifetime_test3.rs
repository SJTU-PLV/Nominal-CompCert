enum S<'a,'b>{
    x(&'a mut &'b mut i32),
    y(&'a mut i32)
}

fn main(){
    let mut v1 = 1;
    let mut p = &mut v1;
    let mut x = S::x(&mut p);
    let mut dummy = 1;
    match x{
        S::x(r) =>{
            // r: &'a mut &'b mut i32
            let mut q = &mut *r;// 'q2: 'b, 'b: 'q2
            // if we use symbolic pointers, we need to relate *q and *r to the same pointee
            let mut tmp = 4;
            *q = &mut tmp; // 'tmp: 'q2
            tmp = 4;
            **r = 5 // 'tmp extends to here because ('tmp: 'q2: 'b)
        },
        S::y(_)=>{
            dummy = 2
        }
    }
}