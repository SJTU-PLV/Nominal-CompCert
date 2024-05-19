fn main(){
    let a: Box<i32> = Box(1);
    let p: &mut i32 = &mut *a;
    a = Box(2);
    printf("%d", *p);
}