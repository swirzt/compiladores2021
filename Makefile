all:
	stack run -- -c test/$a.fd4
	gcc runtime.c test/$a.c -lgc -w -o program -O3
	./program