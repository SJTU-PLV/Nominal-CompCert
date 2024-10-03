#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "util.h"
#include "linked_list.h"
#include "hash_map.h"

struct S { 
	int a; 
	double b;
};

DEFINE_LIST_NODE(double)

void print_node_double(void *ppl)
{
	LIST_NODE(double) *pl = ppl;
	printf("pl has the value {val: %f, next: %x}\n", pl->val, pl->next);
}

int compare_double(void *pval, void *pnode)
{
	double *pv = pval;
	double *pn = pnode;

	// printf("Comparing %f, %f\n", *pv, *pn);

	if (*pv < *pn)
		return -1;
	else if (*pn < *pv)
		return 1;
	else
		return 0;
}

DEFINE_HASH_MAP_ITEM(double, int)

void print_item_double_int(void *item)
{
	hash_map_item_double_int *it = item;
	printf("(%f, %d); ", it->key, it->val);
}

int main()
{
	struct S s = {10, 0.22};
	struct S *p = TEMP_VAL_ADDR(s);
	printf("S has the value {a: %d, b: %f}\n", p->a, p->b);

	int a = 10;
	int *ip = TEMP_VAL_ADDR(a + 10);
	printf("Value of 'a + 10' is: %d\n", *ip);

	LIST_NODE(double) b = {1.2, NULL};
	printf("S has the value {val: %f, next: %x}\n", b.val, b.next);

	LIST_NODE(double)* pl = NULL;
	for (int i = 0; i < 10; i++) 
		LL_INSERT(double, pl, i * 3.14159);
	LL_MAP(double, pl, print_node_double);

	LIST_NODE(double) **ppl = 
		LL_FIND(double, pl, 3.14159, compare_double);
	printf("The found addr is: %x\n", *ppl);
	print_node_double(*ppl);

	LL_REMOVE(double, *ppl);
	print_node_double(*ppl);
	LL_REMOVE(double, *ppl);
	assert (*ppl == NULL);

	LL_DELETE(double, pl);

	
	void *hm = HMAP_NEW();
	HASH_MAP_ITEM(double, int) *it;
	for (int i = 0; i < 20; i++) 
		HMAP_SET(double, int, hm, (rand()%1000)/100.0, rand()%99);
	HMAP_PRINT(double, int, hm, print_item_double_int);
	HMAP_SET(double, int, hm, 0.46, 100);
	HMAP_PRINT(double, int, hm, print_item_double_int);
	it = HMAP_GET(double, int, hm, 0.46);
	printf("item is (%f, %d)\n", it->key, it->val);
	it = HMAP_GET(double, int, hm, -0.58);
	assert(it == NULL);

	HMAP_DELETE(double, int, hm);

	return 0;
}
