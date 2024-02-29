all : test run

run: 
	#dune exec --profile release -- analyzer -f foo c/simple-test.c -sf c/simple-test.spec
	dune exec --profile release -- analyzer -f sin_dbl c/test-sin.c -sf c/test-sin.spec
	#dune exec --profile release -- analyzer -f foo c/test-nan.c -sf c/test-nan.spec
	#dune exec --profile release -- analyzer -f foo c/test-sbenz.c -sf c/test-sbenz.spec
	#dune exec --profile release -- analyzer -f foo c/test1.c -sf c/test1.spec
	#dune exec --profile release -- analyzer -f determinant c/test3.c -sf c/test3.spec

test: clean
	dune exec --profile release -- analyzer -test

clean:
	dune clean

build:
	dune build
