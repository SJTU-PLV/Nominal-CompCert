include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS_GCC=$(CCOMPOPTS) -stdlib ../../runtime -dc -dclight -dasm
CCOMPFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -relf
CFLAGS=-O1 -Wall

# set simulator
## 32bit
# SIMU_LIB_DIR=~/riscv/sysroot
# SIMU=qemu-riscv32 -L $(SIMU_LIB_DIR)
## 64bit
SIMU_LIB_DIR=/usr/riscv64-linux-gnu/
SIMU=qemu-riscv64 -L $(SIMU_LIB_DIR)

LIBS=$(LIBMATH)

# TIME=ocaml unix.cma ../../tools/xtime.ml -o /dev/null -mintime 2.0 -minruns 4
TIME=ocaml unix.cma ../../tools/xtime.ml -o /dev/null -repeat 30

PROGS=fib integr qsort fft fftsp fftw sha1 sha3 aes almabench \
  lists binarytrees fannkuch knucleotide mandelbrot nbody \
  nsieve nsievebits spectral vmach \
  bisect chomp perlin siphash24

all: $(PROGS:%=%.compcert)

all_compcert_gcc: $(PROGS:%=%.compcert_gcc)

all_s: $(PROGS:%=%.s)

all_gcc: $(PROGS:%=%.gcc)

all_myelf: $(PROGS:%=%.myelf)

all_myelf_gcc: $(PROGS:%=%.myelf_gcc)

%.compcert: %.c
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)

%.compcert_gcc: %.c
	$(CCOMP) $(CCOMPFLAGS_GCC) -o $*.compcert_gcc $*.c $(LIBS)

%.myelf: %.c
	$(CCOMP) $(CCOMPFLAGS) -c $*.c -o $*.myelf $(LIBS)

%.myelf_gcc: %.c
	$(CCOMP) $(CCOMPFLAGS_GCC) -c $*.c -o $*.myelf_gcc $(LIBS)

%.s: %.c
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) -o $*.gcc $*.c $(LIBS)

test:
	@for i in $(PROGS); do \
	   if $(SIMU) ./$$i.compcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; exit 2; \
	   fi; \
         done

test_gcc:
	@for i in $(PROGS); do \
	   if ./$$i.gcc | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

bench_gcc:
	@for i in $(PROGS); do \
	   $(TIME) -name $$i -- $(SIMU) ./$$i.compcert_gcc; \
         done

bench:
	@for i in $(PROGS); do \
	   $(TIME) -name $$i -- $(SIMU) ./$$i.compcert; \
         done

bench_space:
	@for i in $(PROGS); do \
		ls -l $$i.myelf;\
		done

bench_gcc_space:
	@for i in $(PROGS); do \
		ls -l $$i.myelf_gcc;\
		done

clean:
	rm -f *.compcert *.gcc *.realasm *.compcert_gcc
	rm -f *.myelf *.myelf_gcc
	rm -f *.compcert.c *.light.c *.parsed.c *.s *.o *.sdump *~ 
