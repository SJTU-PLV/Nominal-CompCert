struct list_node;
enum list;

struct list_node {
    first : i32;
    second : Box<list>;
};

enum list {
    nil(),
    cons(list_node),
};

fn pop_and_push(l: Box<list>, v: i32) -> Box<list> {
    let head : list_node;
    head.first = v;
    match *l {
        list::nil => {      
            let tl' : list  = tl;
            head.second = Box(tl');
        } 
        list::cons => {
            head.second = tl.second;
        }
    }
    let ret : list = head;
    return Box(ret);
}

fn main(){
    let l : list = nil();
    let head : list_node;
    head.first = 42;
    head.second = Box(l);
    l = head;
    let l' : Box<list> = push_and_pop(Box(l), -2);  
}