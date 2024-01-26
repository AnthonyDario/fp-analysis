run: clean
	dune exec analyzer --profile release c/test.c

test: clean
	dune exec --profile release -- analyzer -test

clean:
	dune clean

build:
	dune build
