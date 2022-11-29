#!/bin/bash
SRC=$1.compcert
SRC_GCC=$1.compcert_gcc
TOOLPREFIX=~/riscv/bin/riscv32-unknown-linux-gnu-
# TOOLPREFIX=
READELF=${TOOLPREFIX}readelf
OBJDUMP=${TOOLPREFIX}objdump 

TAG_READELF=$1.readelf
TAG_GCC_READELF=$1.readelf_gcc

TAG_OBJDUMP=$1.objdump
TAG_GCC_OBJDUMP=$1.objdump_gcc

rm -f ${SRC} ${SRC_GCC}

make ${SRC}
make ${SRC_GCC}

${READELF} -a ${SRC} > ${TAG_READELF}
${READELF} -a ${SRC_GCC} > ${TAG_GCC_READELF}
${OBJDUMP} -D ${SRC} > ${TAG_OBJDUMP}
${OBJDUMP} -D ${SRC_GCC} > ${TAG_GCC_OBJDUMP}