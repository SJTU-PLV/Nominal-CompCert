#include<stdlib.h>

typedef struct{
    Link* next;
    Link* prev;
} Link;


extern struct Node;

// RELY: the return value is equal to N
extern size_t link_offset();

Link empty_link(){
    Link link;
    link.next = NULL;
    link.prev = NULL;
    return link;
}

// For now we cannot return a struct, so we return a heap-allocated object.
// This function create the link in the node. It links 'next' and 'prev' to n
// RELY:
// * n must only contain one node (i.e., the link in its field must be NULL)
Link* create_link(struct Node* n){
    Link* head = (unsigned char*)n + link_offset();
    head->next = head;
    head->prev = head;
    return n;
}

// RELY: 
// * l and n must be not null
// * the location of (l + offset_of()) and (n + offset_of()) must be
//   semantically well-typed of Link
struct List* push_front(struct Node* l, struct Node* n){
    Link* head = (unsigned char*)l + link_offset();
    Link* first = (unsigned char*)n + link_offset();
    Link* prev = head->prev;
    first->next = head;
    first->prev = prev;
    prev->next = first;
    head->prev = first;
    return l;
}

// pop_front only pop out the first element and then return the rest of the list. May be we can use some callback function to operate on the value being popped
// RELY:
// * The list must have at least **two** elements (May be we should add option type...)
// * The node to be popped must be release
struct List* pop_front(struct Node* l){
    Link* head = (unsigned char*)l + link_offset();
    Link* next = head->next;
    Link* new_head = (unsigned char*)l - link_offset();
    free(head);
    return new_head;
}

int is_single(struct Node*l){
    Link* head = (unsigned char*)l + link_offset();
    if (head->next == head) return 1;
    else return 0;
}