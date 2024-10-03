#include <stdio.h>
#include <assert.h>
#include "vector.h"
#include "hash_map.h"


typedef struct person {
	char name[80];
	size_t age;
	double height;
} person;

DEFINE_VECTOR(double)
DEFINE_VECTOR(person)

/*
void test(double **vec)
{
	void *v;                                                       
	v = malloc(2 * sizeof(size_t) + VEC_DEFAULT_CAP * sizeof(double));  
	printf("%x\n", v);                                             
	if (v != NULL) {                                               
	        ((size_t *)v)[0] = VEC_DEFAULT_CAP;                        
                ((size_t *)v)[1] = 0;                                      
                *vec = (double *)((size_t *)v + 2);                             
                printf("%x\n", *vec);                                      
	} else {                                                       
		*vec = NULL;				                   
	}                                                              
}
*/

void print_doubles(double *arr, int n)
{
	int i;

	for (i = 0; i < n; i++)
		printf("%f; ", arr[i]);
	printf("\n");
}

person random_person()
{
	person p;
	int i;

	for (i = 0; i < 10; i++)
		p.name[i] = (rand() % 26 + 'a');
	p.name[11] = 0;
	p.age = rand() % 100 + 1;
	p.height = (rand() % 200) / 100.0;

	return p;
}

void print_persons(person *arr, int n)
{
	int i;
	
	for (i = 0; i < n; i++)
		printf("name: \"%s\"; age: %ld; height: %f\n",
		       arr[i].name, arr[i].age, arr[i].height);
}

DEFINE_HASH_MAP_ITEM(person, int)

void print_item_person_int(void *item)
{
	hash_map_item_person_int *it = item;
	printf("key: ");
	print_persons(&it->key, 1);
	printf("val: %d\n", it->val);
}

int main()
{
	double *v;
	// test(&v);
	v = VEC_NEW(double);
	VEC_PRINT_META_DATA(double, v);
	
	for (int i = 0; i < 20; i++) {
		VEC_PUSH(double, v, (double)i);
		// VEC_PRINT_META_DATA(double, v);
	}
	VEC_PRINT_META_DATA(double, v);
	VEC_REMOVE(double, v, 10);
	VEC_REMOVE(double, v, 15);
	VEC_REMOVE(double, v, 20);
	VEC_PRINT_META_DATA(double, v);
	print_doubles(v, VEC_SIZE(double, v));

	VEC_DELETE(double, v);

	person *p;
	p = VEC_NEW(person);
	for (int i = 0; i < 20; i++) {
		VEC_PUSH(person, p, random_person());
	}
	VEC_PRINT_META_DATA(person, p);
	print_persons(p, VEC_SIZE(person, p));
	VEC_REMOVE(person, p, 10);
	VEC_REMOVE(person, p, 15);
	VEC_PRINT_META_DATA(person, p);
	print_persons(p, VEC_SIZE(person, p));

	VEC_DELETE(person, p);	

	void *hm = HMAP_NEW();
	person ss;
	for (int i = 0; i < 20; i++) {
		person s = random_person();
		HMAP_SET(person, int, hm, s, rand()%100);
		if (i == 10)
			ss = s;
	}
	HMAP_PRINT(person, int, hm, print_item_person_int);
	printf("Get item:\n");
	print_item_person_int(HMAP_GET(person, int, hm, ss));
	person sss = ss;
	strcpy(sss.name, "AAA");
	assert (HMAP_GET(person, int, hm, sss) == NULL);
	HMAP_SET(person, int, hm, ss, -14);
	print_item_person_int(HMAP_GET(person, int, hm, ss));
	HMAP_DELETE(person, int, hm);

	return 0;
}
