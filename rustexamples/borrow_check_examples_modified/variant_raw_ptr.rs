enum list{
    nil,
    cons(* mut i32)
}

fn main(){
    let mut v : i32 = 12;
    let p : &mut i32 = &mut v;
    let l1 : list = list::cons(p as *mut i32); // reintepret_cast
    v = 13;
    match l1 {
        list::nil => { 
            printf("No");
        }
        list::cons(r) => {
            *r = 14;
        }
    }

}
