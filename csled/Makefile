include ../Makefile.config

CXX_FILES = $(shell ls|xargs -I'{}' find {} -name "*.cc")

O_FILES =  $(CXX_FILES:%.cc=%.o)

GENERATED_DIR = generated

all: generator
ifeq ($(ARCH), x86)
	./generator x86/x86.csled
else
ifeq ($(ARCH), riscV)
	./generator riscv/riscv.csled
endif
endif
	mv generated/VerificationCondition.v ../autogen
	mv generated/EncDecRet.v ../autogen

generator: parser src
	g++  -std=c++11 $(O_FILES) syntax.tab.o lex.yy.o  -g -o generator
	mkdir -p $(GENERATED_DIR)

src:  parser $(O_FILES)

lexical: parser/lexical.l syntax
	flex $<
	g++  -std=c++11 -c lex.yy.c -g

syntax: parser/syntax.y
	bison $< -v -d
	mv syntax.tab.cc syntax.tab.cpp
	g++  -std=c++11 -c syntax.tab.cpp -g

parser:  syntax lexical


%.o: %.cc parser
	g++  -std=c++11 -DFOO -c $< -g -o $@
	


lex.yy.o: lexical.l
	flex $<
	g++ -c lex.yy.c


syntax.tab.o: syntax.y
	bison $< -v -d
	mv syntax.tab.cc syntax.tab.cpp
	g++ -c syntax.tab.cpp

# generator.out: syntax.tab.o lex.yy.o $(O_FILES)    
# 	g++ $(O_FILES) syntax.tab.o lex.yy.o -ly -lfl -o $@


clean:
	rm -f generator
	rm -f *.out
	rm -f $(O_FILES)
	rm -f $(GENERATED_DIR)/*
	rm -f lex.yy.c
	rm -f *.tab.cpp
	rm -f *.tab.hh
	rm -f location.hh
	rm -f *.output
	rm -f lex.yy.o
	rm -f syntax.tab.o
	ls|xargs -I'{}' find {} -name "*.vo"|xargs rm -f
	ls|xargs -I'{}' find {} -name "*.vos"|xargs rm -f
	ls|xargs -I'{}' find {} -name "*.vok"|xargs rm -f
	ls|xargs -I'{}' find {} -name "*.aux"|xargs rm -f
	ls|xargs -I'{}' find {} -name "*.glob"|xargs rm -f
	ls|xargs -I'{}' find {} -name "*.o"|xargs rm -f


COQCINCLUDE= -R coq/lib lib\
-R coq/utils utils\
-R coq/flocq Flocq\
-R generated/ csled

FLOCQ_FILES=$(shell find coq/flocq -name "*.v")

COQ_FILES=coq/lib/Bits.v coq/lib/Coqlib.v\
coq/lib/Encode.v coq/lib/Errors.v\
coq/lib/Hex.v coq/lib/Integers.v\
coq/lib/Util.v coq/lib/Zbits.v\
coq/lib/Archi.v coq/lib/AST.v coq/lib/Values.v\
coq/lib/Memdata.v coq/lib/Maps.v\
coq/lib/Floats.v coq/lib/IEEE754_extra.v\
coq/utils/BPProperty.v\
coq/utils/ListDestruct.v\
evaluation/Extraction.v\
$(FLOCQ_FILES)

GEN_COQ_FILES=$(GENERATED_DIR)/BFtrue.v\
$(GENERATED_DIR)/VerificationCondition.v\
$(GENERATED_DIR)/EncDecRet.v $(GENERATED_DIR)/RelSpec.v\
$(GENERATED_DIR)/EncConsistency.v $(GENERATED_DIR)/DecConsistency.v\
$(GENERATED_DIR)/Soundness.v

# proof: $(COQ_FILES:%.v=%.vo)

%.vo: %.v
	@echo "COQC $*.v"
	@coqc $(COQCINCLUDE) $*.v

depend:
	ls $(COQ_FILES)|xargs coqdep $(COQCINCLUDE) > .depend

gendep:
	ls $(GEN_COQ_FILES) $(COQ_FILES)| xargs coqdep $(COQCINCLUDE) > .depend

CoqProject:
	@echo $(COQCINCLUDE) > _CoqProject


# parser: formac mac
# 	mv parser.mac parser.out

smt:
	python3 smt-parser.py

proof: CoqProject gendep $(GEN_COQ_FILES:%.v=%.vo)

-include .depend
