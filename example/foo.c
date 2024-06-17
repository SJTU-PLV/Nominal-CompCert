#include <stdio.h>
extern void foo1();
extern void foo2();
 
int foo(){
  int a = 0;
  foo1();
  a = 2;
  foo2();
  return a;
}
