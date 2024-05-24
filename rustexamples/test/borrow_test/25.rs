struct list<'a>;

enum list_node<'a>;

enum list_node<'a> {
    None,
    Some(&'a mut list<'a>)
}

struct list<'a> {
    value: i32,
    next: list_node<'a>
}

fn sum<'a>(l: &'a mut list<'a>) -> i32 {
    let result: i32 = 0;
    loop {
        result = result + (*l).value;
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

fn add_one<'a>(l: &'a mut list) {
    loop {
        (*l).value = (*l).value + 1;
        match (*l).next {
            list_node::Some(ref mut r) => {
                l = &mut **r;
            }
            list_node::None => {
                break;
            }
        }
    }
}

fn main(){
    let l0: list = list {value: 1, next: list_node::None(())};
    let l1: list = list {value: 2, next: list_node::Some(&mut l0)};
    let l2: list = list {value: 3, next: list_node::Some(&mut l1)};
    add_one(&mut l2);
    printf("Sum of list is %d", sum(&mut l2));
}