#!/bin/bash
LIB_DIR=~/riscv/sysroot
EMU=qemu-riscv32

${EMU} -L ${LIB_DIR} $1