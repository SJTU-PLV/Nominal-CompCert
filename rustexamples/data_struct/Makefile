TARGET = main
TST-TARGET = tst
CC = gcc
CFLAGS = -g -Wall
OBJECTS = $(patsubst %.c, %.o, $(wildcard *.c))
MAINS = main.o tst.o
NON-MAINS = $(filter-out $(MAINS), $(OBJECTS))

all: $(TARGET)
	@echo "Done."

test: $(TST-TARGET)
	@echo "Done."

$(TST-TARGET): tst.o $(NON-MAINS)

$(TARGET): main.o $(NON-MAINS)

$(OBJECTS): %.o: %.c

util.o: util.h
vector.o: vector.h util.h
linked_list.o: linked_list.h util.h
hash_map.o: hash_map.h util.h
main.o: vector.h util.h
tst.o: util.h linked_list.h hash_map.h


.PHONY: all clean zip

clean:
	rm $(TARGET) *.o

zip: $(wildcard *.c *.h) Makefile
	zip -r data_struct.zip $^
