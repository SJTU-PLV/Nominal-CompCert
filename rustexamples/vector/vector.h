#ifndef __VECTOR_H__

#include <stdlib.h>

/*
 * Default capacity of vectors
 */
#define VEC_DEFAULT_CAP    10

/*
 * Create an empty new vector with default capacity
 */
void *vec_new(size_t elem_size);

/*
 * Delete a vector
 */
void vec_del(void *vec);

/*
 * Erase an element
 * Return non-zero value upon success
 */
int vec_erase(void *vec, size_t idx);

/*
 * Expand the vector if the maximam capacity is reached.
 * Return a non-zero value upon failure
 * The first argument is a pointer of the pointer to the vector.
 * (e.g., pushed an element of wrong size)
 */
int vec_expand(void *pvec);

/*
 * Get the size of the vector
 */
size_t vec_size(void *vec);

/*
 * Increase the size of the vector by 1.
 * Return the old size.
 */
size_t vec_size_post_incr(void *vec);

/*
 * Print the meta-data of vector
 */
void vec_print_meta_data(void *vec);


/*
 * Macro wrappers
 */
#define VEC_NEW(T)              vec_new(sizeof(T))
#define VEC_DEL(vec)            vec_del(vec)
#define VEC_SIZE(vec)           vec_size(vec)
#define VEC_ERASE(vec, idx)     vec_erase(vec, idx)
#define VEC_PUSH(vec, e) \
	((!vec_expand(&vec)) ? ((vec[vec_size_post_incr(vec)] = e), 0) : -1)

#endif
