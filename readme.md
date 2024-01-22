This is a static analysis tool for analyzing the floating point error in
numerical C code.  It is based upon abstract interpretation and uses the novel
abstract domain of step functions to represent the floating point error.

# Dependencies
You will need [CIL](https://github.com/goblint/cil) installed:

```
opam install goblint-cil
```

# Running
Run the tests with `make`.
