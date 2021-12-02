all:
	stack run -- -c test/$a.fd4
	gcc runtime.c test/$a.c -lgc -w -o program -O3
	./program

# Para compilar pedantico
# stack build --pedantic --ghc-options -Wno-type-defaults --ghc-options -Wno-missing-signatures --ghc-options -Wno-missing-pattern-synonym-signatures --ghc-options -Wno-unused-do-bind