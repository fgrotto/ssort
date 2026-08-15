CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -pedantic -std=c11
LDFLAGS ?= -lm
SAN     ?= -fsanitize=address,undefined -fno-sanitize-recover=all

.PHONY: all lib test fuzz asan clean

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

# Differential fuzzer against a heap-Dijkstra + Bellman-Ford oracle.
fuzz: fuzz.c ssort.c ssort.h
	$(CC) $(CFLAGS) fuzz.c ssort.c -o $@ $(LDFLAGS)
	./fuzz 1 30 6000

# Sanitizer build: unit tests + a short fuzz run.
asan: test_asan fuzz_asan
	./test_asan
	./fuzz_asan 7 10 3000

test_asan: test_ssort.c ssort.c ssort.h
	$(CC) -O1 -g -Wall -Wextra -pedantic -std=c11 $(SAN) test_ssort.c ssort.c -o $@ $(LDFLAGS)

fuzz_asan: fuzz.c ssort.c ssort.h
	$(CC) -O1 -g -Wall -Wextra -pedantic -std=c11 $(SAN) fuzz.c ssort.c -o $@ $(LDFLAGS)

clean:
	rm -f *.o *.a test_ssort fuzz test_asan fuzz_asan
