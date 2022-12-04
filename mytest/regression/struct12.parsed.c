extern void __builtin_debug(int kind, ...);

extern int printf(char const * restrict __format, ...);

struct s;

struct s {
  unsigned char a[256];
};

union u;

struct _380;

struct _380 {
  struct s b;
  int c;
};

struct _381;

struct _381 {
  int c;
  struct s b;
};

union u {
  struct _380 d;
  struct _381 e;
};

static union u v;

static struct s * q = &v.e.b;

static struct s * zp = &v.d.b;

static void __attribute__((__structreturn)) rp(struct s * _res)
{
  *_res = *zp;
  return;
}

static void qp(void)
{
  struct s _res;
  rp(&_res), *q = _res;
}

int main(void)
{
  int i;
  for (i = 0; i < 256; i++) {
    zp->a[i] = i;
  }
  qp();
  for (i = 0; i < 256; i++) {
    if (q->a[i] != i) {
      printf("ERROR at %d: %d\n", i, q->a[i]);
    }
  }
  return 0;
  return 0;
}


