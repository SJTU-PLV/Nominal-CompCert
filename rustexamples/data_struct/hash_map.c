#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "hash_map.h"

void* hmap_new()
{
	size_t n = DEFAULT_HASH_MAP_LENGTH;
	void **hm;
	size_t i;

	hm = malloc(sizeof(void *) * n);
	
	if (hm == NULL)
		return NULL;
	for (i = 0; i < n; i++)
		hm[i] = NULL;

	return hm;
}

void *hmap_bucket_set(void *pbucket, size_t node_size, size_t next_ofs, 
		      void *pitem, size_t item_size, size_t key_size)
{
	void **pn;
	nbytes *key_bytes = nbytes_new(pitem, key_size);
	void *result;

	pn = ll_find(pbucket, next_ofs, key_bytes, compare_nbytes);
	if (*pn == NULL) {
	        if (!ll_insert(pn, node_size, next_ofs, pitem, item_size)) {
			result = *pn;
			goto FREE;
		}
		else {
			result = NULL;
			goto FREE;
		}
	}
	memcpy(*pn, pitem, item_size);
	result = *pn;

FREE:
	free(key_bytes);
	return result;
}

void *hmap_bucket_get(void *pbucket, size_t next_ofs, void *pkey, size_t key_size)
{
	void **pn;
	nbytes *key_bytes = nbytes_new(pkey, key_size);
	void *result;
	
	pn = ll_find(pbucket, next_ofs, key_bytes, compare_nbytes);
	if (*pn == NULL) {
		result = NULL;
		goto FREE;
	}
	result = *pn;

FREE:
	free(key_bytes);
	return result;
}

void hmap_delete(void *hm, size_t next_ofs)
{
	size_t n = DEFAULT_HASH_MAP_LENGTH;
	size_t i;

	for (i = 0; i < n; i++)
		ll_delete(((void **)hm)[i], next_ofs);

	free(hm);
}

void hmap_print(void *hm, size_t next_ofs, void (*print_item) (void *item))
{
	size_t i;
	
	for (i = 0; i < DEFAULT_HASH_MAP_LENGTH; i++) {
		printf("Slot %ld: ", i);
		ll_map(((void **)hm)[i], next_ofs, print_item);
		printf("\n");
	}
}
