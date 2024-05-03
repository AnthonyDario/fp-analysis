all : test run

run: clean
	#dune exec --profile release -- analyzer -f main c/kalman/kettle.c -sf c/kalman/kettle.spec
	#dune exec --profile release -- analyzer -f foo c/simple-array-test.c -sf c/simple-array-test.spec
	dune exec --profile release -- analyzer -f axb_33 c/bench/matmul3x3.c -sf c/bench/matmul3x3.spec

test: clean
	dune exec --profile release -- analyzer -test

clean:
	dune clean

build:
	dune build
