#include <stdio.h>
#include <string.h>
#include "vector.h"

void *vec_new(size_t elem_size) 
{                  
	void *v;                                                       
	v = malloc(3 * sizeof(size_t) + VEC_DEFAULT_CAP * elem_size);
	// fprintf(stderr, "Created Vector at: 0x%x\n", v);
	if (v != NULL) {                                               
	        ((size_t *)v)[0] = VEC_DEFAULT_CAP;                        
                ((size_t *)v)[1] = 0;                                      
                ((size_t *)v)[2] = elem_size;
                return (size_t *)v + 3;
	}

	return NULL;
}

void vec_del(void *vec) 
{         
	vec = (size_t *)vec - 3;  
	// fprintf(stderr, "Deleted Vector at: 0x%x\n", vec);
	free(vec);
}

int vec_expand(void *pvec)
{
	void *new_vec;
	size_t *vsz;
	size_t old_cap, cur_size, new_cap, elem_size;

	vsz = *((size_t **)pvec) - 3;
	old_cap = vsz[0];
	cur_size = vsz[1];
	elem_size = vsz[2];
	
	if (old_cap != cur_size) 
		return 0;

	new_cap = old_cap * 2 + 1;
	new_vec = realloc(vsz, 
			  3 * sizeof(size_t) + new_cap * elem_size);
	if (new_vec == NULL)
		goto EXPANSION_FAILURE;
	vsz = new_vec;
	vsz[0] = new_cap;
	*((size_t **)pvec) = vsz + 3;

	return 0;

EXPANSION_FAILURE:
	return -1;
}

int vec_erase(void *vec, size_t idx)
{
	size_t *vsz;
	size_t cur_size, elem_size;

	vsz = (size_t *)vec - 3;
	cur_size = vsz[1];
	elem_size = vsz[2];

	if (idx >= cur_size)
		goto OUT_OF_INDEX;

	memmove((char *)vec + idx * elem_size,
		(char *)vec + (idx + 1) * elem_size,
		(cur_size - idx - 1) * elem_size);
	vsz[1]--;

	return 0;

OUT_OF_INDEX:
	return -1;
}


size_t vec_size_post_incr(void *vec)
{
	size_t *vsz;

	vsz = (size_t *)vec - 3;
	return vsz[1]++;
}

size_t vec_size(void *vec)
{
	size_t *vsz;

	vsz = (size_t *)vec - 3;
	return vsz[1];
}

void vec_print_meta_data(void *vec)
{
	size_t *vsz;
	vsz = (size_t *)vec - 3;

	printf("Capacity: %ld; Size: %ld; Element Size: %ld\n", 
	       vsz[0], vsz[1], vsz[2]);
}

