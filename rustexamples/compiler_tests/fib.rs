fn fib(n: i32) -> i32 {
    if (n < 2) {
        return 1;
    }
    else {
        return fib(n - 1) + fib(n - 2);
    }
}

fn main(){
    let n: i32;
    let r: i32;
    n = 35;
    r = fib(n);
    printf("fib(%d) = %d\n", n, r);
}