#include <string.h>
#include <stdlib.h>
#include "util.h"

nbytes *nbytes_new(void *bytes, size_t size)
{
	nbytes *nb;

	nb = malloc(sizeof(nbytes) + size);
	if (nb == NULL)
		return NULL;
	nb->size = size;
	memcpy(nb->data, bytes, size);

	return nb;
}

int compare_nbytes(void *bytes, void *other)
{
	int result;
	nbytes *bs = bytes;

	result = memcmp(bs->data, other, bs->size);
	return result;
}

