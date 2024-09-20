#ifndef LINKED_LIST
#define LINKED_LIST

#include<stdlib.h>

struct Link;

void insert_after(struct Link* before, struct Link* after);
struct Link* remove_after(struct Link* before);
struct Link* get_pos(struct Link*head, size_t pos);
struct Link* get_next(struct Link* node);

#endif