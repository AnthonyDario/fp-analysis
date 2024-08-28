This is a static analysis tool for analyzing the floating point error in
numerical C code.  It is based upon abstract interpretation and uses the novel
abstract domain of step functions to represent the floating point error.

# Dependencies
First, install OCaml from [here](https://ocaml.org/install).

You will need [CIL](https://github.com/goblint/cil) and ocaml rounding
modes installed:

```
opam pin add -y round git@github.com:tyabu12/ocaml-round.git
opam install goblint-cil round
```

# Running

The tool ingests a C file and a "specification file".  Examples can be found in
the `c` directory.  

Run with `dune exec -- <C-FILE> -f <FUN> -sf <SPEC-FILE>`.  Replace `<C-FILE>`
with the file you want to analyze, `<FUN>` with the function you are analyzing,
and `<SPEC-FILE>` with the specification file.  Examples of invocations can be
found in the makefile.

The specification file format is a list of variable bounds such as:
```
x = {([2;4], 0.001), ([4;8], 0.0001)}
y = {([1;3], 0.003), ([3;6], 0.0003)}
```
The above declares the bounds for two variables, each with two different
segments.  `x`'s value is between 2 and 8, with two different errors
associated with different regions of the interval. 

Run the tests with `make test`.
