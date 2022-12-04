#!/bin/bash
SRC=$1.compcert
SRC_ELF=$1.myelf
SRC_GCC=$1.compcert_gcc
TOOLPREFIX=~/riscv/bin/riscv32-unknown-linux-gnu-
# TOOLPREFIX=
READELF=${TOOLPREFIX}readelf
OBJDUMP=${TOOLPREFIX}objdump 

TAG_MYELF=$1.myelf.readelf
TAG_READELF=$1.readelf
TAG_GCC_READELF=$1.readelf_gcc

TAG_OBJDUMP=$1.objdump
TAG_GCC_OBJDUMP=$1.objdump_gcc

rm -f ${SRC} ${SRC_GCC} ${SRC_ELF}

make ${SRC}
make ${SRC_GCC}
make ${SRC_ELF}

${READELF} -a ${SRC_ELF} > ${TAG_MYELF}
${READELF} -a ${SRC} > ${TAG_READELF}
${READELF} -a ${SRC_GCC} > ${TAG_GCC_READELF}
${OBJDUMP} -D ${SRC} > ${TAG_OBJDUMP}
${OBJDUMP} -D ${SRC_GCC} > ${TAG_GCC_OBJDUMP}