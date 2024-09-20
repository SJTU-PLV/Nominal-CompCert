#include"linked_list.h"

/* bytes offset of the link field from the start of its associated struct */
extern size_t offset_of();

struct Data;

typedef struct{
    struct Link* head;
} IntList;

struct Data* pop_nth_element(IntList* l, size_t n){
    if(l->head != NULL){
        /* get the previous node to do removal */
        struct Link* prev = get_pos(l->head, n-1);
        if (prev != NULL){
            struct Link* nth = remove_after(prev);
            /* get the data struct pointer */
            struct Data* data = (unsigned char*)nth - offset_of();
            return data;
        }
    }
    /* no such data pointer */
    return NULL;
}

void map(IntList* l, struct Data*f(struct Data*)){
    /* TODO */
}

void push_front(IntList* l, struct Data* data){
    
}