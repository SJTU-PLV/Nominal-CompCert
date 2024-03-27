enum E {
    a: i32,
    b: i32
}

fn f() -> i32 {
    return 1;
}

fn main() {
    let e: E = E::a(0);
    let x: i32 = f();
    if x < 1 {
        let y: i32 = 0;
    }
    return y;
}
