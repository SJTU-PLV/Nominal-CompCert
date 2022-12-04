#!/bin/bash
LIB_DIR=~/riscv/sysroot
EMU=qemu-riscv32

rm -f $1
make $1
${EMU} -L ${LIB_DIR} $1