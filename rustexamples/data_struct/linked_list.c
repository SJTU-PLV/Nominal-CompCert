#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "linked_list.h"

int ll_insert(void *pnext, size_t node_size, size_t next_ofs,
	      void *pval, size_t val_size)
{
	char **pn = pnext;
	char *new_node;

	if ((new_node = malloc(node_size)) == NULL)
		goto ALLOC_FAILURE;

	memcpy(new_node, pval, val_size);
	*(void **)(new_node + next_ofs) = *pn;
	*pn = new_node;

	return 0;

ALLOC_FAILURE:
	return -1;
}

void ll_map(void *node, size_t next_ofs, void (*f)(void *))
{
	while (node != NULL) {
		f(node);
		node = *(void **)((char *)node + next_ofs);
	}
}

void *ll_find(
	void *pnext, size_t next_ofs, void *pval, 
	int (*cmp)(void *pval, void *pnode)
){
	char **pn = pnext;
	
	while (*pn != NULL) {
		if (!cmp(pval, *pn))
			return pn;
		pn = (char**)(*pn + next_ofs);
	}

	return pn;
}

void ll_remove(void *pnext, size_t next_ofs)
{
	char **pn = pnext;
	char *pnn;

	if (*pn == NULL)
		return;

	pnn = *(char **)(*pn + next_ofs);
	free(*pn);
	*pn = pnn;
}

void ll_delete(void *node, size_t next_ofs)
{
	char *pnode = node;
	char *pnext;
	size_t n = 0;

	while (pnode != NULL) {
		pnext = *(char **)(pnode + next_ofs);
		free(pnode);
		pnode = pnext;
		n++;
	}

	// fprintf(stderr, "Removed %d nodes upon deletion\n", n);
}
