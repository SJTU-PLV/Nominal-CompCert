struct List;

enum Option {
    Some(Box<List>),
    None()
}

struct List {
    data: u32,
    next: Option,
}

struct S<'s> {
    v: u32,
    p: &'s u32,
}

struct S1<'s> {
    v: u32,
    p: &'s mut u32,
}

fn print_all(mut p: &mut List) {
    loop {
        printf("%u", p.data);
        match &mut p.next {
            Some(n) => {
                p = n;
            }
            None => {
                break;
            }
        }
    }
}

fn max_ref<'c, 'a: 'c, 'b: 'c>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32 {
    if *a > *b {
        return a;
    } else {
        return b;
    }
}

fn max_ref1<'a>(a: &'a mut i32, b: &'a mut i32) -> &'a mut i32 {
    let p :&mut i32= &mut *a;
    *b = 5;
    *p = 4;

    if *a > *b {
        return a;
    } else {
        return b;
    }
}

fn two_ref_andS<'a, 'b, 'c>(a: &'a u32, b: &'b u32, c: S<'c>) {}

fn main() {
    let v: u32 = 12;
    let p1: &u32 = &v;
    let p2: &u32 = &v;
    let s: S = S { v: 3, p: &v };
    two_ref_andS(p1, p2, s);
}
