enum list<'a, 'b>{
    dummy(&'b mut i32),
    cons(&'a mut i32, Box<list<'a, 'b>>)
}

// we test reference in box which is in an enum
enum list1<'a,'b>{
    dummy(&'b mut i32),
    cons(Box<&'a mut i32>, Box<list1<'a, 'b>>)
}

// list : {'a: Aptr1, 'b: Aptr2}

// We cannot treat enum as a whole abstract pointer, because here
// consider dummy(x) and cons(y,_), x and y do not alias. But if we
// change 'b to 'a in dummy, the rustc borrow checker treat x and y
// alias with each other, and the following code compiles error.

fn main(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut x = 1;
    let mut y = 2;
    let l0 = list::cons(&mut v1, Box::new(list::dummy(&mut x)));
    // l0 = {'a: {&mut v1}, 'b: {&mut x}}
    let l1 = list::cons(&mut v2, Box::new(l0));
    // l1 = {'a : {&mut v2}, 'b: {}}
    // how to merge l0 to l1
    // l1 = {'a : {&mut v1, &mut v2}, 'b: {&mut x}}
    match l1 {
        list::dummy(_) => v3 = 4,
        list::cons(r, _) =>
            { x = 2; // x does not alias r, how to represent it in abstract value
              *r = 5 }
    };
}

fn test_list1(){
    let mut v1 = 1;
    let mut v2 = 2;
    let mut v3 = 3;
    let mut x = 1;
    let mut y = 2;
    let l0 = list1::cons(Box::new(&mut v1), Box::new(list1::dummy(&mut x)));
    // l0 = {'a: {&mut v1}, 'b: {&mut x}}
    let l1 = list1::cons(Box::new(&mut v2), Box::new(l0));
    // l1 = {'a : {&mut v2}, 'b: {}}
    // how to merge l0 to l1
    // l1 = {'a : {&mut v1, &mut v2}, 'b: {&mut x}}
    match l1 {
        list1::dummy(_) => v3 = 4,
        list1::cons(r, _) =>
            { // v2 = 3; // r alias with v2 and v1 , error
              v1 = 3; // error
              **r = 5 }
    };
}
 
