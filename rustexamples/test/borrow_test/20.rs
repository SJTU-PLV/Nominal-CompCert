fn main(){
    let x: i32 = 22;
    let y: i32 = 44;
    let p: & i32 = &x;
    y = y + 1;
    let q: & i32 = &y;
    if x < y {
        p = q;
        x = x + 1;
    } else {
        y = y + 1;
    }
    y = y + 1;
    printf("%d", *p);
}