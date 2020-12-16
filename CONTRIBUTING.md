# Contributing to the Iris Coq Development

Here you can find some how-tos for various thing sthat might come up when doing
Iris development.  This is for contributing to Iris itself; see
[the README](README.md#further-resources) for resources helpful for all Iris
users.

To work on Iris itself, you need to install its build-dependencies.  Again we
recommend you do that with opam (2.0.0 or newer).  This requires the following
two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make builddep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update Iris, do `git pull`.  After an update, the development may fail to
compile because of outdated dependencies.  To fix that, please run `opam update`
followed by `make builddep`.

## How to submit a merge request

To contribute code, you need an MPI-SWS GitLab account as described on the
[chat page](https://iris-project.org/chat.html).  Then you can fork the
[Iris git repository][iris], make your changes in your fork, and create a merge
request.  If forking fails with an error, please send your MPI-SWS GitLab
username to [Ralf Jung][jung] to unlock forks for your account.

Please do *not* use the master branch of your fork, that might confuse CI.  Use
a feature branch instead.

[jung]: https://gitlab.mpi-sws.org/jung
[iris]: https://gitlab.mpi-sws.org/iris/iris

## How to update the std++ dependency

* Do the change in std++, push it.
* Wait for CI to publish a new std++ version on the opam archive, then run
  `opam update iris-dev`.
* In Iris, change the `opam` file to depend on the new version.
  (In case you do not use opam yourself, you can see recently published versions
  [in this repository](https://gitlab.mpi-sws.org/iris/opam/commits/master).)
* Run `make builddep` (in Iris) to install the new version of std++.
  You may have to do `make clean` as Coq will likely complain about .vo file
  mismatches.

## How to write/update test cases

The files in `tests/` are test cases.  Each of the `.v` files comes with a
matching `.ref` file containing the expected output of `coqc`.  Adding `Show.`
in selected places in the proofs makes `coqc` print the current goal state.
This is used to make sure the proof mode prints goals and reduces terms the way
we expect it to.  You can run `make MAKE_REF=1` to re-generate all the `.ref` files;
this is useful after adding or removing `Show.` from a test.  If you do this,
make sure to check the diff for any unexpected changes in the output!

Some test cases have per-Coq-version `.ref` files (e.g., `atomic.8.8.ref` is a
Coq-8.8-specific `.ref` file).  If you change one of these, remember to update
*all* the `.ref` files.

If you want to compile without tests run `make NO_TEST=1`.

## How to build/install only one package

Iris is split into multiple packages that can be installed separately via opam.
You can invoke the Makefile of a particular package by doing `./make-package
$PACKAGE $MAKE_ARGS`, where `$MAKE_ARGS` are passed to `make` (so you can use
the usual `-jN`, `install`, ...).  This should only rarely be necessary. For
example, if you are not using opam and you want to install only the `iris`
package (without HeapLang, to avoid waiting on that part of the build), you can
do `./make-package iris install`.  (If you are using opam, you can achieve the
same by pinning `coq-iris` to your Iris checkout.)

Note that `./make-package` will never run the test suite, so please always do a
regular `make -jN` before submitting an MR.

## How to measure the timing effect on a reverse dependency

So say you did a change in Iris, and want to know how it affects [lambda-rust]
or the [examples].  To do this, check out the respective project and change its
`.gitlab-ci.yml` to contain only one build job, which should look like
```
build-iris.dev:
  <<: *template
  variables:
    OPAM_PINS: "coq version 8.12.0   coq-iris.dev git git+https://gitlab.mpi-sws.org/iris/iris.git#yourname/feature   coq-iris-heap-lang.dev git git+https://gitlab.mpi-sws.org/iris/iris.git#yourname/feature"
  tags:
  - fp-timing
```
You will have to adjust this a bit: you should use the same Coq version as
whatever the master branch uses for its timing job, which you can determine by
checking its `.gitlab-ci.yml`.  You will also have to adjust the Iris branch
being used, which is determined after the `#` in `OPAM_PINS`.  If the repo you
are testing does not need HeapLang, you can remove the `coq-iris-heap-lang` part
of `OPAM_PINS`.  If you are in doubt, ask on Mattermost *before* pushing your
branch.  Please double-check that the job name is `build-iris.dev` to avoid
polluting the caches of regular CI builds!  This way, you are going to share the
cache with the nightly builds, which is fine.

Once you are confident with your CI configuration, push this to a new branch
whose name starts with `ci/`.  It should usually be of the form
`ci/yourname/feature`.  You should see a pipeline running in GitLab with just a
single job, and you can follow its progress there.

When the job is done, you should be able to see it as a single dot on our
[statistics server][coq-speed] after selecting the right project and branch.
Click on "Coq-Speed" on the top-left corner to switch to another dashboard, and
select "Coq-Compare".  Now you can select the project and the two measurements
you want to compare, which would be the SHA of the commit you just created as
"Commit 2", and the SHA of its parent as "Commit 1".  Don't forget to also
select the right configuration for both of them.  The "Grouping" is a regular
expression that you can use to switch between per-file, per-directory and
per-project grouping of the measurements.

If you changed your Iris branch and want to make another measurement, *do not*
just "Retry" the CI job.  That will lead to an error, because you would end up
with two measurements for the same commit.  Instead, create an empty commit in
your branch of the to-be-measured project (`git commit --allow-empty -m
"rerun"`), and push that.

[lambda-rust]: https://gitlab.mpi-sws.org/iris/lambda-rust
[examples]: https://gitlab.mpi-sws.org/iris/examples
[coq-speed]: https://coq-speed.mpi-sws.org
