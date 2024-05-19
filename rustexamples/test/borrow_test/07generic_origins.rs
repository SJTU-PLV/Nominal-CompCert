fn main() {
    let v: i32 = 1;
    let p: &i32 = &v;
	let q : &i32 = return_ref(p, &v);
    printf("%d", *q);
}

fn return_ref<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 
    where 'b: 'a
{
    let a : i32 = *x;
    return &*y;
}
