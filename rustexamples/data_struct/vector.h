#ifndef __VECTOR_H__

#include <stdlib.h>
#include "util.h"

/*
 * Default capacity of vectors
 */
#define VEC_DEFAULT_CAP    10

/*
 * Get the name of the vector
 */
#define VECTOR(T)         VECTOR_(T)
#define VECTOR_(T)        vector_##T

/*
 * Define the vector type
 */
#define DEFINE_VECTOR(T) 	      	\
	typedef struct VECTOR(T) { 	\
	    size_t capacity;            \
	    size_t size;                \
	    size_t item_size;           \
            T items[];                  \
	} VECTOR(T);

/*
 * Create an empty new vector with default capacity
 */
void *vec_new(size_t header_size, size_t item_size);

/*
 * Delete a vector
 */
void vec_delete(void *vec, size_t header_size);

/*
 * Remove an element
 * Return non-zero value upon success
 */
int vec_remove(void *vec, size_t header_size, size_t idx);

/*
 * Expand the vector if the maximam capacity is reached.
 * Return a non-zero value upon failure
 * The first argument is a pointer of the pointer to the vector.
 * (e.g., pushed an element of wrong size)
 */
int vec_expand(void *pvec, size_t header_size);

/*
 * Get the size of the vector
 */
size_t vec_size(void *vec, size_t header_size);

/*
 * Push a value to the end of the vector.
 * The first argument has the type T**.
 * Expand the vector if the maximum capacity is reached.
 * Return non-zero upon failure.
 */
int vec_push(void *pvec, size_t header_size, void *pval, size_t size);

/*
 * Print the meta-data of vector
 */
void vec_print_meta_data(void *vec, size_t header_size);


/*
 * Macro wrappers
 */
#define VEC_NEW(T)                vec_new(sizeof(VECTOR(T)), sizeof(T))
#define VEC_DELETE(T, vec)        vec_delete(vec, sizeof(VECTOR(T)))
#define VEC_SIZE(T, vec)          vec_size(vec, sizeof(VECTOR(T)))
#define VEC_REMOVE(T, vec, idx)   vec_remove(vec, sizeof(VECTOR(T)), idx)
#define VEC_PUSH(T, vec, e)       vec_push(&vec, sizeof(VECTOR(T)), \
					   TEMP_VAL_ADDR(e), sizeof(e))
#define VEC_PRINT_META_DATA(T, vec) \
	vec_print_meta_data(vec, sizeof(VECTOR(T)))

#endif
