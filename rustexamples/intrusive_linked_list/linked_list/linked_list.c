#include"linked_list.h"

typedef struct{
    Link* next;
} Link;

void insert_after(Link* before, Link* after){
    after->next = before -> next;
    before->next = after;
}

/* remove the link next to before and return this link. before must be
non-null */
Link* remove_after(Link* before){
    Link* after = before->next;
    if(after != NULL){
        before->next = after->next;
    }
    return after;
}

Link* get_pos(Link*head, size_t pos){
    /* TODO */
    return NULL;
}

Link* get_next(Link* node){
    return node->next;
}