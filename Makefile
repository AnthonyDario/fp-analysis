all : test run

run: 
	dune exec --profile release -- analyzer -f foo c/test-sbenz.c -sf c/test-sbenz.spec
	#dune exec --profile release -- analyzer -f foo c/test1.c -sf c/test1.spec
	#dune exec --profile release -- analyzer -f determinant c/test3.c -sf c/test3.spec

test: clean
	dune exec --profile release -- analyzer -test

clean:
	dune clean

build:
	dune build
