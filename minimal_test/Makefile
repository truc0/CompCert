all: fib.s run

fib.s: fib.c
	../ccomp -timings -S -v fib.c

fib.o: fib.c
	../ccomp -timings -c -relf -v fib.c

fib.asm: fib.o
	objdump -S fib.o > fib.asm

run: fib.o fib.asm
	gcc -m32 -o fib fib.o
	./fib 1
	./fib 2
	./fib 3
	./fib 4
	./fib 5
	./fib 6
	./fib 7
	./fib 8

clean:
	rm -rf fib fib.o fib.s fib.asm

.PHONY: run clean all

