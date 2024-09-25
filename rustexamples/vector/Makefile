TARGET = main
CC = gcc
CFLAGS = -g -Wall
OBJECTS = $(patsubst %.c, %.o, $(wildcard *.c))

all: $(TARGET)
	@echo "Done."

$(TARGET): $(OBJECTS)

$(OBJECTS): %.o: %.c

vector.o: vector.h
main.o: vector.h


.PHONY: all clean

clean:
	rm $(TARGET) *.o
