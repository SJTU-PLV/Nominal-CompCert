#include<stdlib.h>

// Parameter N represents the offset of Link in the data struct
// Parameter sem_wt_Data

typedef struct{
    Link* next;
} Link;

extern struct Data;

// RELY: the return value is equal to N
extern size_t link_offset();

// RELY: 
// * l and n must be not null
// * the location of (l + offset_of()) and (n + offset_of()) must be
//   semantically well-typed of Link
struct Data* push_front(struct Data* l, struct Data* n){
    Link* head = (unsigned char*)l + link_offset();
    Link* first = (unsigned char*)n + link_offset();
    first->next = head;
    return n;
}

Link empty_link(){
    Link l = {.next = NULL};
    return l;
}


// GOAL: to prove total safety under the rust ownership interface. This proof can be parametrized by a parameter N representing the offset of Link field in Data type and a predicate which describes the semantics type of Data

// Incoming invariant (proof of ownership interface):
// * world := (function_name, symbol tale, footprint, memory)
// * query_inv (id, se, fp, m) (vf, args, m) := id = push_front -> sem_wt_Data l fp1 m /\ sem_wt_Data n fp2 m /\ fp = fp1 * fp2 
// * reply_inv (id, se, fp, m) (rv, m) := exists fp', fp ~-> fp' /\ 
//                                          (id = push_front -> exists fpr, sem_wt_Data rv fpr m /\ fpr \in fp') /\
//                                          (id = empty_link -> ...)

// Outgoing invariant (only link_offset):
// * world := (function_name, symbol tale)
// * query_inv (id, se) (vf, args, m) := True
// * reply_inv (id, se) (rv, m) := id = link_offset -> rv = N