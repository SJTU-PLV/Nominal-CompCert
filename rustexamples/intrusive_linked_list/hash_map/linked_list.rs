enum List;
struct Node;

struct Node {
    key: i32,
    val : i32,
    next : Box<List>
}

enum List {
    Nil,
    Cons(Node)
}

extern fn process(k: i32, v: i32) -> i32

fn hash(k: i32, range: i32) -> i32{
    return k % range;
}

// use callback function instead of returning the value?
fn find(l: Box<List>, k: i32) -> Box<List>{
    match *l {
        List::Nil => {
            // *l = List::Nil; l is not moved out
            return l;
        }
        List::Cons(node) => {
            if (k == node.key) {
                node.val = process(k, node.val);
                *l = List::Cons(node);
                return l;
            }
            else {
                node.next = find(node.next, k);
                *l = List::Cons(node);
                return l
            }
        }
    }
}

fn empty_list() -> Box<List> {
    return Box(List::Nil);
}

fn insert(l: Box<List>, k: i32, v: i32) -> Box<List>{
    let head: Node = Node{key: k, val: v, next: l};
    l = Box(List::Cons(head));
    return l;
}

fn remove(l: Box<List>, k: i32) -> Box<List>{
    match *l {
        List::Nil => {
            // *l = List::Nil;
            return l;
        }
        List::Cons(node) => {
            if (k == node.key) {
                return node.next;
            }
            else {
                node.next = remove(node.next, k);
                *l = List::Cons(node);
                return l;
            }
        }
    }
}

fn delete_list(l: Box<List>){
    return;
}