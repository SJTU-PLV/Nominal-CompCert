fn choose<'c, 'a: 'c, 'b: 'c>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32{
    &mut *a
}

/*fn assign<'a,'b,'c>(input: &'a mut &'b str, val: &'c str) {
    *input = val;
}*/

// fn assign1<'a, 'b>(mut a: &'a mut i32, mut b: &'b mut i32){
//     a = b;
//     b = a;
// }

fn origin_subset_post_cond<'b, 'a: 'b>(a: &'a i32, b: &'b i32) -> &'b i32{
    a
}

fn origin_subset_post_cond_mut1<'b, 'a: 'b>(a: &'a mut i32, b: &'b mut i32){
    *a = *b;
}

fn origin_subset_post_cond_mut2<'b, 'a: 'b>(a: &'a mut i32, b: &'b mut i32) -> &'b mut i32{
    a
}

fn test(){
    let mut v1 = 1;
    let mut v2 = 2;
    let p = &mut v1;
    let q = &mut v2;
    origin_subset_post_cond_mut1(p, q); // do we have 'p:'q constrain here?
    // let m = origin_subset_post_cond_mut2(p,q);
    v1 = 2;
    *q = 3;
}

fn main(){
    let mut v1 = 1;
    let mut v2 = 2;
    let p = & v1;
    let q = & *p; //'p:'q
    let m = origin_subset_post_cond(q,p); // no error!
    // here we generate a new constraint 'q:'p from origin_subset_post
}