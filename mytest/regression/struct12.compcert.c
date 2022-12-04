struct s;
struct _380;
struct _381;
union u;
struct s {
  unsigned char a[256];
};

struct _380 {
  struct s b;
  int c;
};

struct _381 {
  int c;
  struct s b;
};

union u {
  struct _380 d;
  struct _381 e;
};

static unsigned char const __stringlit_1[17];

static union u v;

static struct s *q;

static struct s *zp;

static void rp(struct s *);

static void qp(void);

extern int main(void);

unsigned char const __stringlit_1[17] = "ERROR at %d: %d\012";

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

extern int printf(unsigned char *, ...);

union u v;

struct s *q = (void *)((char *)&v + 4);

struct s *zp = &v;

void rp(struct s *_res)
{
  *_res = *zp;
  return;
}

void qp(void)
{
  struct s _res;
  rp(&_res), *q = _res;
}

int main(void)
{
  int i;
  for (i = 0; i < 256; i++) {
    *(((*zp)).a + i) = i;
  }
  qp();
  for (i = 0; i < 256; i++) {
    if (*(((*q)).a + i) != i) {
      printf(__stringlit_1, i, *(((*q)).a + i));
    }
  }
  return 0;
  return 0;
}


