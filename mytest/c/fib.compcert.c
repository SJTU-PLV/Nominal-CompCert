static unsigned char const __stringlit_1[14];

extern int fib(int);

extern int main(int, unsigned char **);

unsigned char const __stringlit_1[14] = "fib(%d) = %d\012";

extern unsigned int __compcert_va_int32(void *);

extern unsigned long long __compcert_va_int64(void *);

extern double __compcert_va_float64(void *);

extern void *__compcert_va_composite(void *, unsigned int);

extern void __compcert_va_saveregs(void);

extern long long __compcert_i64_dtos(double);

extern unsigned long long __compcert_i64_dtou(double);

extern double __compcert_i64_stod(long long);

extern double __compcert_i64_utod(unsigned long long);

extern float __compcert_i64_stof(long long);

extern float __compcert_i64_utof(unsigned long long);

extern long long __compcert_i64_sdiv(long long, long long);

extern unsigned long long __compcert_i64_udiv(unsigned long long, unsigned long long);

extern long long __compcert_i64_smod(long long, long long);

extern unsigned long long __compcert_i64_umod(unsigned long long, unsigned long long);

extern long long __compcert_i64_shl(long long, int);

extern unsigned long long __compcert_i64_shr(unsigned long long, int);

extern long long __compcert_i64_sar(long long, int);

extern long long __compcert_i64_smulh(long long, long long);

extern unsigned long long __compcert_i64_umulh(unsigned long long, unsigned long long);

extern void __builtin_debug(int, ...);

extern int atoi(unsigned char *);

extern int printf(unsigned char *, ...);

int fib(int n)
{
  if (n < 2) {
    return 1;
  } else {
    return fib(n - 1) + fib(n - 2);
  }
}

int main(int argc, unsigned char **argv)
{
  int n;
  int r;
  if (argc >= 2) {
    n = atoi(*(argv + 1));
  } else {
    n = 35;
  }
  r = fib(n);
  printf(__stringlit_1, n, r);
  return 0;
  return 0;
}


