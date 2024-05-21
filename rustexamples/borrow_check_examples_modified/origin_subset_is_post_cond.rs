fn choose<'c, 'a: 'c, 'b: 'c>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32{
    &mut *a
}

fn origin_subset_post_cond<'b, 'a: 'b>(a: &'a i32, b: &'b i32) -> &'b i32{
    a
}

fn origin_subset_post_cond_mut1<'b, 'a: 'b>(a: &'a mut i32, b: &'b mut i32){
    *a = *b;
}

fn origin_subset_post_cond_mut2<'b, 'a: 'b>(a: &'a mut i32, b: &'b mut i32) -> &'b mut i32{
    a
}

fn test() {
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let p: &mut i32 = &mut v1;
    let q: &mut i32 = &mut v2;
    origin_subset_post_cond_mut1(p, q); 
    v1 = 2;
    *q = 3;
}

fn main() {
    let mut v1: i32 = 1;
    let mut v2: i32 = 2;
    let p: &i32 = &v1;
    let q: &i32 = &*p; 
    // unsupported 'static
    let m: &'static i32 = origin_subset_post_cond(q, p);
}