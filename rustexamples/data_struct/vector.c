#include <stdio.h>
#include <string.h>
#include "vector.h"

DEFINE_VECTOR(int)

void *vec_new(size_t header_size, size_t item_size) 
{                  
	VECTOR(int) *v;                                                       
	v = malloc(header_size + VEC_DEFAULT_CAP * item_size);
	// fprintf(stderr, "Created Vector at: 0x%x\n", v);
	if (v != NULL) {                                               
	        v->capacity = VEC_DEFAULT_CAP;                        
                v->size = 0;                                      
                v->item_size = item_size;
                return (char*)v + header_size;
	}

	return NULL;
}

void vec_delete(void *vec, size_t header_size) 
{         
	vec = (char*)vec - header_size;
	// fprintf(stderr, "Deleted Vector at: 0x%x\n", vec);
	free(vec);
}

int vec_remove(void *vec, size_t header_size, size_t idx)
{
	VECTOR(int) *pheader;
	size_t cur_size, item_size;

	pheader = (VECTOR(int) *)((char *)vec - header_size);
	cur_size = pheader->size;
	item_size = pheader->item_size;

	if (idx >= cur_size)
		goto OUT_OF_INDEX;

	memmove((char *)vec + idx * item_size,
		(char *)vec + (idx + 1) * item_size,
		(cur_size - idx - 1) * item_size);
	pheader->size--;

	return 0;

OUT_OF_INDEX:
	return -1;
}

int vec_expand(void *pvec, size_t header_size)
{
	void *new_vec;
	VECTOR(int) *pheader;
	size_t old_cap, cur_size, new_cap, item_size;

	pheader = (VECTOR(int) *)(*(char**)pvec - header_size);
	old_cap = pheader->capacity;
	cur_size = pheader->size;
	item_size = pheader->item_size;
	
	if (old_cap != cur_size) 
		return 0;

	new_cap = old_cap * 2 + 1;
	new_vec = realloc(pheader,
			  header_size + new_cap * item_size);
	if (new_vec == NULL)
		goto EXPANSION_FAILURE;
	pheader = new_vec;
	pheader->capacity = new_cap;
	*(char **)pvec = (char *)pheader + header_size;

	return 0;

EXPANSION_FAILURE:
	return -1;
}

size_t vec_size(void *vec, size_t header_size)
{
	VECTOR(int) *pheader;

	pheader = (VECTOR(int) *)((char *)vec - header_size);
	return pheader->size;
}

int vec_push(void *pvec, size_t header_size, void *pval, size_t size)
{
	VECTOR(int) *pheader;
	size_t cur_size, item_size;

	if (vec_expand(pvec, header_size))
		goto EXPANSION_FAILURE;

	pheader = (VECTOR(int) *)(*(char **)pvec - header_size);
	cur_size = pheader->size;
	item_size = pheader->item_size;
	
	if (item_size != size)
		goto SIZE_MISMATCH;

	memcpy(*(char **)pvec + cur_size * item_size, pval, size);
	pheader->size++;

	return 0;

EXPANSION_FAILURE:
	return -1;
SIZE_MISMATCH:
	return -2;
}

void vec_print_meta_data(void *vec, size_t header_size)
{
	VECTOR(int) *pheader;
	pheader = (VECTOR(int) *)((char *)vec - header_size);

	printf("Capacity: %ld; Size: %ld; Item Size: %ld\n", 
	       pheader->capacity,
	       pheader->size,
	       pheader->item_size);
}

