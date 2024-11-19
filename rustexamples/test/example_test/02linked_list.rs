enum list;
struct list_node;

struct list_node {
    value : i32,
    next : Box<list>
}

enum list {
    nil,
    cons(list_node)
}

// It pops an element from a list and then pushes [v] in the list
fn pop_and_push(l: Box<list>, v: i32) -> Box<list> {
    let head : list_node;
    head.value = v;
    match *l {
        list::nil => {      
            head.next = Box(list::nil);
        } 
        list::cons(tl) => {
            head.next = tl.next;
        }
    };
    let ret : list = list::cons(head);
    return Box(ret);
}

// fn main(){
//     let l : list = list::nil;
//     let head : list_node;
//     head.first = 42;
//     head.second = Box(l);
//     l = head;
//     let l1 : Box<list> = push_and_pop(Box(l), -2);  
// }
