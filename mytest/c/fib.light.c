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
int fib(int);
int main(int, unsigned char **);
unsigned char const __stringlit_1[14] = "fib(%d) = %d\012";

int fib(int n)
{
  register int $63;
  register int $62;
  if (n < 2) {
    return 1;
  } else {
    $62 = fib(n - 1);
    $63 = fib(n - 2);
    return $62 + $63;
  }
}

int main(int argc, unsigned char **argv)
{
  int n;
  int r;
  register int $63;
  register int $62;
  if (argc >= 2) {
    $62 = atoi(*(argv + 1));
    n = $62;
  } else {
    n = 35;
  }
  $63 = fib(n);
  r = $63;
  printf(__stringlit_1, n, r);
  return 0;
  return 0;
}


