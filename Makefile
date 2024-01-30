run:
	dune exec --profile release -- analyzer -f determinant c/test3.c

test: clean
	dune exec --profile release -- analyzer -test

clean:
	dune clean

build:
	dune build
