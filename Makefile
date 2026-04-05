CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -pedantic -std=c11
LDFLAGS ?= -lm

.PHONY: all lib test clean

all: lib test

lib: libssort.a

libssort.a: ssort.o
	$(AR) rcs $@ $^

ssort.o: ssort.c ssort.h
	$(CC) $(CFLAGS) -c $< -o $@

test: test_ssort
	./test_ssort

test_ssort: test_ssort.c ssort.c ssort.h
	$(CC) $(CFLAGS) test_ssort.c ssort.c -o $@ $(LDFLAGS)

clean:
	rm -f *.o *.a test_ssort
