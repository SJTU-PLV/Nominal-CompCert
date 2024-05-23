fn choose<'c, 'a, 'b>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32
    where 'a: 'c, 'b: 'c
{
    return &mut *a;
}

fn main(){
    let v1: i32 = 1;
    let v2: i32 = 2;
    let p: &mut i32 = choose(&mut v1, &mut v2);
    v2 = 3;
    *p = 4;
}