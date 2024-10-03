#ifndef __LINKED_LIST_H__
#define __LINKED_LIST_H__

#include <stddef.h>
#include "util.h"

/*
 * Get the name of the list node 
 */
#define LIST_NODE(T)     LIST_NODE_(T)
#define LIST_NODE_(T)    list_node_##T

/*
 * A single node in the linked list
 */
#define DEFINE_LIST_NODE(T) 	      	\
	typedef struct LIST_NODE(T) { 	\
	    T val;			\
	    struct LIST_NODE(T) *next;  \
	} LIST_NODE(T);


/*
 * Given a pointer to the cell containing the pointer
 * to the next node, insert a new list node.
 * The arguments are:
 * 
 *   LIST_NODE(T) **pnext   // Pointer to the cell pointing to the next node
 *   node_size              // Size of the list node
 *   next_ofs               // Offset to the next pointer in a node
 *   T *pval                // Pointer to the value
 *   val_size               // Size of the value
 *
 * The function returns non-zero upon failure.
 */
int ll_insert(void *pnext, size_t node_size, size_t next_ofs,
	      void *pval, size_t val_size);

/*
 * Iterate over the list and apply the given function to each node
 */
void ll_map(void *node, size_t next_ofs, void (*f)(void *));

/*
 * Given a pointer to the cell containing the pointer
 * to the next node, find the node matching
 * the given value in a linked list.
 * The arguments are:
 * 
 *   LIST_NODE(T) **pnext   // Pointer to the cell pointing to the next node
 *   next_ofs               // Offset to the next pointer in a node
 *   T *pval                // Pointer to the value
 *   cmp                    // Function for comparing the value and the values
 *                          // in the searched nodes. The comparison returns 0
 *                          // if they are equal, -1 if the value is smaller and
 *                          // 1 if the value is larger.
 *
 * The function returns the pointer to the cell pointing to the found node.
 * If no such node is found, the pointer to the last next field (which
 * contains NULL) is returned.
 */
void *ll_find(void *pnext, size_t next_ofs, void *pval, 
	      int (*cmp)(void *pval, void *pnode));

/*
 * Given a pointer to the cell poining to the next node.
 * Remove the next node from the linked list.
 * If the next node is NULL, this method has no effect.
 */
void ll_remove(void *pnext, size_t next_ofs);

/*
 * Delete the entire linked list
 */
void ll_delete(void *node, size_t next_ofs);

/*
 * MACROS for list operations
 */
#define LIST_NODE_NEXT_OFS(T)   \
	offsetof(LIST_NODE(T), next)
#define LL_INSERT(T, l, v)   			  \
	ll_insert(&l, 				  \
		sizeof(LIST_NODE(T)),	          \
		LIST_NODE_NEXT_OFS(T),            \
		TEMP_VAL_ADDR(v), sizeof(v))
#define LL_MAP(T, l, f)   \
	ll_map(l, LIST_NODE_NEXT_OFS(T), f)
#define LL_FIND(T, l, v, cmp)                          \
	ll_find(&l, LIST_NODE_NEXT_OFS(T),             \
		TEMP_VAL_ADDR(v), cmp)

#define LL_REMOVE(T, l)   \
	ll_remove(&l, LIST_NODE_NEXT_OFS(T))
#define LL_DELETE(T, l)   \
	ll_delete(l, LIST_NODE_NEXT_OFS(T))

#endif
