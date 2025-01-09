
struct Node{
    val: i32;
    link: Link;
}

extern Link {size: 16; align: 16}

extern fn empty_link() -> Link;

extern fn push_front(Box<Data> l, Box<Data> n) -> Box<Data>;

fn link_offset() -> u64{
    return 16;
}

fn create(v: i32) -> Box<Node> {
    let head : Box<Node> = Box(Node{val: v, link: empty_link()});
    return create_link(head);
}

fn push(l: Box<Node>, v: i32) -> Box<Node> {
    let head: Box<Node> = Box(Node {val: v, link: empty_link()});
    l = push_front(l, head);
    return l;
}