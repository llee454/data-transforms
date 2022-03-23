README
======

This package contains a formally verified library of data transformation
functions that can be used for data analysis. It consists of a Coq library and a
wrapping OCaml library. The Coq library can be used directly, but we intend for
users to generally use the OCaml library. This OCaml library provides two
versions of each function, a slower formally verified implementation and a
faster version tested using unit tests. When compiling, users can select which
implementation to bind to the library interface.

This library provides functions to search, filter, join, and group over data
sets. This library assumes that you have a dataset stored within a SQL database,
that you are extracting data from this database using SQL queries, and that you
are analyzing this data in OCaml. Performing complex queries in SQL is error
prone. SQL is untyped and has subtle behaviors. Therefore, this library provides
functions that perform the same operations that are commonly performed in
complex SQL queries. This enables you to avoid subtle SQL errors by performing
complex operations outside of SQL.

Initializing the Build Environment
----------------------------------

Note: the following are a hack solution to fix the fact that brew and opam are
out of sync and opam's owl-plplot library requires library versions that can no
longer be installed with brew.

```
opam switch create . ocaml-variants.4.10.0+flambda --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install --deps-only .
dune build
dune exec src/main.exe
```

Note: Coq can use either Makefiles or Dune files to build projects. We use Dune
files to compile Coq files into the OCaml library, and local Makefiles to
compile the Coq code independently. Use the following commands to generate the
Coq Makefiles and compile the Coq library independently.

```
coq_makefile -f _CoqProject > Makefile
make
```

Use `make clean` to remove Coq files before running `dune build`.

Execution
---------

Use the following command fo execute the demo script which outputs the results
of a sample analysis:

```
dune exec src/main.exe
```