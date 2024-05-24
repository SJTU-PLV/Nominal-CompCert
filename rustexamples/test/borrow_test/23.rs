struct list;

enum list_node;

enum list_node {
    None,
    Some(Box<list>)
}

struct list {
    value: i32,
    next: list_node
}

fn sum<'a>(l: &'a mut list) -> i32 {
    let result: i32 = 0;
    loop {
        result = result + *l.value;
        match (*l).next {
            list_node::Some(ref mut r) => {
                l = &mut **r;
            }
            list_node::None => {
                return result;
            }
        }
    }
    return result;
}

fn main(){
    
}