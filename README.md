# `coqar`

`coqar` is an implementation of `ar` with `Coq` and the `FreeSpec` library.
This allows to certify the correctness of the implementation.

## Requirements

- Coq (version 8.9)
- FreeSpec ([github](https://github.com/ANSSI-FR/FreeSpec))

## Compilation

First, the interface `FileSystem` of the `FreeSpec.exec` plugin must be installed:

```
cd fileSystem
./configure
make
make install
```

Then, `coqar` can be compiled and installed:

```
cd ar
./configure
make
make install
```

## Running `coqar`

```
coqc ar/Main.v
```

It will use the argument list provided in `Main.v`.
