#ifndef __HASH_MAP_H__
#define __HASH_MAP_H__

#include "util.h"
#include "linked_list.h"

/*
 * A hash map is an array of buckets (linked lists).
 * Each bucket contains a list of elements with its index as the hash key.
 */

#define DEFAULT_HASH_MAP_LENGTH    7

/*
 * The item stored in hash map nodes is a pair
 * of key and value
 */
#define HASH_MAP_ITEM(K, T)      HASH_MAP_ITEM_(K, T)
#define HASH_MAP_ITEM_(K, T)     hash_map_item_##K##_##T
#define DEFINE_HASH_MAP_ITEM(K, T)            \
	typedef struct HASH_MAP_ITEM(K, T) {  \
            K key;  	                      \
	    T val;  		              \
	} HASH_MAP_ITEM(K, T);                \
        DEFINE_LIST_NODE(HASH_MAP_ITEM(K, T))


/*
 * Create a hash map with the default length.
 * Returns a dynamic array of pointers to linked lists.
 */
void* hmap_new();

/*
 * Delete the entire hash map
 */
void hmap_delete(void *hm, size_t next_ofs);

/*
 * Set the item into the hash map.
 *
 *   void **pbucket:  the bucket for storing the item
 *   node_size     :  size of nodes in the buckets
 *   next_ofs      :  offset to next pointers in the list nodes
 *   pitem         :  pointer to the item to be inserted
 *   item_size     :  size of the item
 *   key_size      :  size of the key
 *
 * The function searches for the item with the given key in the bucket.
 * If no such item is found, a new node is inserted to the end of the bucket.
 * Otherwise, it overwrites the founded item with the new value.
 * 
 * It returns the pointer to the set item. NULL is returned upon errors.
 */
void *hmap_bucket_set(void *pbucket, size_t node_size, size_t next_ofs, 
		      void *pitem, size_t item_size, size_t key_size);

/*
 * Get an item from the hash map.
 * 
 *   void **pbucket:  the bucket for storing the item
 *   next_ofs      :  offset to next pointers in the list nodes
 *   pkey          :  pointer to the key to search for the item
 *   key_size      :  size of the key
 *
 * The function searches for the item with the given key in the bucket.
 * If no such item is found or an error occurs, NULL is returned.
 * Otherwise, it returns a pointer to the found item.
 */
void *hmap_bucket_get(void *pbucket, size_t next_ofs, void *pkey, size_t key_size);

/*
 * Print the hash_map
 */
void hmap_print(void *hm, size_t next_ofs, void (*print_item) (void *));

/*
 * Macro wrappers
 */
#define KEY_TO_INDEX(key)    \
	(*(size_t *)(TEMP_VAL_ADDR(key))) % DEFAULT_HASH_MAP_LENGTH
#define HMAP_NEW()            		hmap_new()          
#define HMAP_SET(K, T, hm, key, val) 			    \
	hmap_bucket_set(			  	    \
		(void **)hm + KEY_TO_INDEX(key),	    \
		sizeof(LIST_NODE(HASH_MAP_ITEM(K, T))),     \
		LIST_NODE_NEXT_OFS(HASH_MAP_ITEM(K, T)),    \
		(&(HASH_MAP_ITEM(K, T)){key, val}),         \
		sizeof(HASH_MAP_ITEM(K, T)), 		    \
		sizeof(K)                                   \
	)
#define HMAP_GET(K, T, hm, key)				    \
	hmap_bucket_get(				    \
		(void **)hm + KEY_TO_INDEX(key),	    \
		LIST_NODE_NEXT_OFS(HASH_MAP_ITEM(K, T)),    \
		TEMP_VAL_ADDR(key),				            \
	        sizeof(K)                                   \
        )
#define HMAP_DELETE(K, T, hm) 				    \
	hmap_delete( 					    \
	        hm,					    \
		LIST_NODE_NEXT_OFS(HASH_MAP_ITEM(K, T))     \
        )
#define HMAP_PRINT(K, T, hm, print_item) 		    \
	hmap_print(					    \
	        hm, 					    \
		LIST_NODE_NEXT_OFS(HASH_MAP_ITEM(K, T)),    \
		print_item 				    \
	)

#endif
