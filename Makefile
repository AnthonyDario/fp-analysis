all : test run

run: clean
	dune exec --profile release -- analyzer -f foo c/simple-array-test.c -sf c/simple-array-test.spec
	#dune exec --profile release -- analyzer -f determinant c/bench/determinant3x3.c -sf c/bench/determinant3x3.spec
	#dune exec -- analyzer c/branch-test-simple.c -f foo -sf c/branch-test-simple.spec
	#dune exec --profile release -- analyzer -f foo c/simple-sub-test.c -sf c/simple-sub-test.spec
	#dune exec --profile release -- analyzer -f foo c/branch-test.c -sf c/branch-test.spec
	#dune exec --profile release -- analyzer -f sqroot c/sqrt-test.c -sf c/sqrt-test.spec
	#dune exec --profile release -- analyzer -f sin_dbl c/test-sin.c -sf c/test-sin.spec
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
