# SPDX-License-Identifier: CC0-1.0
#
# `make` builds the command line solver `hpst` (C99, libc + libm only).
#
CC     ?= cc
CFLAGS ?= -O2 -std=c99 -Wall -Wextra -pedantic
LDLIBS  = -lm

hpst: main.o hpst.o
	$(CC) $(CFLAGS) -o $@ main.o hpst.o $(LDLIBS)

main.o: main.c hpst.h
	$(CC) $(CFLAGS) -c main.c

hpst.o: hpst.c hpst.h
	$(CC) $(CFLAGS) -c hpst.c

clean:
	rm -f hpst main.o hpst.o

.PHONY: clean
