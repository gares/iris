# Contributing to the Iris Coq Development

## How to submit a merge request

To contribute code, please send your MPI-SWS GitLab username to
[Ralf Jung](https://gitlab.mpi-sws.org/jung) to enable personal projects for
your account.  Then you can fork the
[Iris git repository](https://gitlab.mpi-sws.org/FP/iris-coq/), make your
changes in your fork, and create a merge request.

Please do *not* use the master branch of your fork, that might confuse CI.  Use
a feature branch instead.

## How to update the std++ dependency

* Do the change in std++, push it.
* Wait for CI to publish a new std++ version on the opam archive, then run
  `opam update iris-dev`.
* In Iris, change the `opam` file to depend on the new version.
* Run `make build-dep` (in Iris) to install the new version of std++.
  You may have to do `make clean` as Coq will likely complain about .vo file
  mismatches.

## How to write/update test cases

The files in `tests/` are test cases.  Each of the `.v` files comes with a
matching `.ref` file containing the expected output of `coqc`.  Adding `Show.`
in selected places in the proofs makes `coqc` print the current goal state.
This is used to make sure the proof mode prints goals and reduces terms the way
we expect it to.  You can run `MAKE_REF=1 make` to re-generate all the `.ref` files;
this is useful after adding or removing `Show.` from a test.  If you do this,
make sure to check the diff for any unexpected changes in the output!

Some test cases have per-Coq-version `.ref` files (e.g., `atomic.8.8.ref` is a
Coq-8.8-specific `.ref` file).  If you change one of these, remember to update
*all* the `.ref` files.
