#include <stdio.h>
#include <assert.h>
#include "vector.h"


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


int main()
{
	double *v;
	// test(&v);
	v = VEC_NEW(double);
	vec_print_meta_data(v);
	
	for (int i = 0; i < 20; i++) {
		VEC_PUSH(v, (double)i);
		// vec_print_meta_data(v);
	}
	vec_print_meta_data(v);
	VEC_ERASE(v, 10);
	VEC_ERASE(v, 15);
	VEC_ERASE(v, 20);
	vec_print_meta_data(v);
	print_doubles(v, VEC_SIZE(v));

	VEC_DEL(v);

	return 0;
}
