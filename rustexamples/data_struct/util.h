#ifndef __UTIL_H__
#define __UTIL_H__

#include <stddef.h>

/*
 * A number of bytes
 */
typedef struct nbytes {
	size_t size;
	char   data[];
} nbytes;

/*
 * Create a bounded number of bytes 
 */
nbytes *nbytes_new(void *bytes, size_t size);

/*
 * Compare a bounded number of bytes
 */
int compare_nbytes(void *bytes, void *other);

/*
 * Create a compond literal array containing the given value.
 * This literal is decayed to its address.
 */
#define TEMP_VAL_ADDR(e) ((typeof(e)[1]){e}) 

#endif
