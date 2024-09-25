// external type
struct Link {size: 8, align: 8}

// Data is not Copy
struct Data {
    val: i32;
    next: Link;
}

extern fn empty_link() -> Link;

extern fn push_front(Box<Data> l, Box<Data> n) -> Box<Data>;

/* push value v in the list l */
fn push(l: Box<Data>, v: i32) -> Box<Data> {
    let head: Data = Data {val: v, next: empty_link()};
    l = push_front(l, head);
    return l;
}

// For circular linked list
fn create(v: i32) -> Box<Data>{
    let head: Data = Data {val: v, next: empty_link()};
    head = link_myself(head)
}

// GUARANTEE: the return value is equal to N in linked_list.c
fn link_offset() -> u64{
    return 8;
}

// GOAL: to prove partial safety
// Assumption: 
// * an oracle (may be symbol table?) containing the semantics type of Link

// Incoming invariant:
// * world := (function_name, symbol tale)
// * query_inv (id, se) (vf, args, m) := True
// * reply_inv (id, se) (rv, m) := id = link_offset -> rv = 8

// Outgoing invariant:
// * world := (function_name, symbol tale)
// * query_inv (id, se) (vf, args, m) := True
// * reply_inv (id, se) (rv, m) := id = push_front -> sem_wt_Data rv (this is rely condition on external call which is not guaranteed by the move checking)
