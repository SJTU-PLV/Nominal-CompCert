fn main() {
    let v: i32 = 1;
    let p: &i32 = &v;
	let q : &i32 = return_ref(p);
    printf("%d", *q);
}

fn return_ref<'a>(x: &'a i32) -> &'a i32 {
    let a : i32 = *x;
    return x;
}
