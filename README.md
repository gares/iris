# IRIS COQ DEVELOPMENT [[coqdoc]](https://plv.mpi-sws.org/coqdoc/iris/)

This is the Coq development of the [Iris Project](http://iris-project.org),
which includes [MoSeL](http://iris-project.org/mosel/), a general proof mode
for carrying out separation logic proofs in Coq.

For using the Coq library, check out the
[API documentation](https://plv.mpi-sws.org/coqdoc/iris/).

For understanding the theory of Iris, a LaTeX version of the core logic
definitions and some derived forms is available in
[tex/iris.tex](tex/iris.tex).  A compiled PDF version of this document is
[available online](http://plv.mpi-sws.org/iris/appendix-3.2.pdf).

## Building Iris

### Prerequisites

This version is known to compile with:

 - Coq 8.10.2 / 8.11.2 / 8.12.0
 - A development version of [std++](https://gitlab.mpi-sws.org/iris/stdpp)

If you need to work with Coq 8.7 or Coq 8.8, please check out the
[iris-3.2 branch](https://gitlab.mpi-sws.org/iris/iris/tree/iris-3.2).
For Coq 8.9, you can use the
[iris-3.3 branch](https://gitlab.mpi-sws.org/iris/iris/tree/iris-3.3).

### Working *with* Iris

To use Iris in your own proofs, we recommend you install Iris via opam (2.0.0 or
newer).  To obtain the latest stable release, you have to add the Coq opam
repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

To obtain a development version, also add the Iris opam repository:

    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Either way, you can now do `opam install coq-iris`.  To fetch updates later, run
`opam update && opam upgrade`.  However, notice that we do not guarnatee
backwards-compatibility, so upgrading Iris may break your Iris-using
developments.

The development version of Iris is regularly subject to breaking changes.  If
you want to be notified of such changes, please let us know your account name on
the [MPI-SWS GitLab](https://gitlab.mpi-sws.org/) so we can add you to the
notification group.

### Working *on* Iris

To work on Iris itself, you need to install its build-dependencies.  Again we
recommend you do that with opam (2.0.0 or newer).  This requires the following
two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update Iris, do `git pull`.  After an update, the development may fail to
compile because of outdated dependencies.  To fix that, please run `opam update`
followed by `make build-dep`.

## Directory Structure

* The folder [algebra](theories/algebra) contains the COFE and CMRA
  constructions as well as the solver for recursive domain equations.
* The folder [base_logic](theories/base_logic) defines the Iris base logic and
  the primitive connectives.  It also contains derived constructions that are
  entirely independent of the choice of resources.
  * The subfolder [lib](theories/base_logic/lib) contains some generally useful
    derived constructions.  Most importantly, it defines composeable
    dynamic resources and ownership of them; the other constructions depend
    on this setup.
* The folder [program_logic](theories/program_logic) specializes the base logic
  to build Iris, the program logic.   This includes weakest preconditions that
  are defined for any language satisfying some generic axioms, and some derived
  constructions that work for any such language.
* The folder [bi](theories/bi) contains the BI++ laws, as well as derived
  connectives, laws and constructions that are applicable for general BIS.
* The folder [proofmode](theories/proofmode) contains
  [MoSeL](http://iris-project.org/mosel/), which extends Coq with contexts for
  intuitionistic and spatial BI++ assertions. It also contains tactics for
  interactive proofs. Documentation can be found in
  [proof_mode.md](docs/proof_mode.md).
* The folder [heap_lang](theories/heap_lang) defines the ML-like concurrent heap
  language
  * The subfolder [lib](theories/heap_lang/lib) contains a few derived
    constructions within this language, e.g., parallel composition.
    For more examples of using Iris and heap_lang, have a look at the
    [Iris Examples](https://gitlab.mpi-sws.org/iris/examples).
* The folder [tests](theories/tests) contains modules we use to test our
  infrastructure. Users of the Iris Coq library should *not* depend on these
  modules; they may change or disappear without any notice.

## Case Studies

The following is a (probably incomplete) list of case studies that use Iris, and
that should be compatible with this version:

* [Iris Examples](https://gitlab.mpi-sws.org/iris/examples) is where we
  collect miscellaneous case studies that do not have their own repository.
* [LambdaRust](https://gitlab.mpi-sws.org/iris/lambda-rust) is a Coq
  formalization of the core Rust type system.
* [GPFSL](https://gitlab.mpi-sws.org/iris/gpfsl) is a logic for release-acquire
  and relaxed memory.
* [Iron](https://gitlab.mpi-sws.org/iris/iron) is a linear separation logic
  built on top of Iris for precise reasoning about resources (such as making
  sure there are no memory leaks).
* [Actris](https://gitlab.mpi-sws.org/iris/actris) is a separation logic
  built on top of Iris for session-type based reasoning of message-passing
  programs.

## Further Resources

Getting along with Iris in Coq:

* Iris proof patterns and conventions are documented in the
  [proof guide](docs/proof_guide.md).
* The Iris tactics are described in the
  [the Iris Proof Mode (IPM) / MoSeL documentation](docs/proof_mode.md) as well as the
  [HeapLang documentation](docs/heap_lang.md).
* The generated coqdoc is [available online](https://plv.mpi-sws.org/coqdoc/iris/).

Contacting the developers:

* Discussion about the Iris Coq development happens on the mailing list
  [iris-club@lists.mpi-sws.org](https://lists.mpi-sws.org/listinfo/iris-club)
  and in the [Iris Chat](https://mattermost.mpi-sws.org/iris).  This is also the
  right place to ask questions.  The chat requires an account at the
  [MPI-SWS GitLab](https://gitlab.mpi-sws.org/users/sign_in) (use the "Register"
  tab). If you have trouble joining the chat, please contact
  [Ralf](https://gitlab.mpi-sws.org/jung).
* If you want to report a bug, please use the
  [issue tracker](https://gitlab.mpi-sws.org/iris/iris/issues), which also
  requires an MPI-SWS GitLab account.
* To contribute to Iris itself, see the [contribution guide](CONTRIBUTING.md).

Miscellaneous:

* Information on how to set up your editor for unicode input and output is
  collected in [editor.md](docs/editor.md).
* If you are writing a paper that uses Iris in one way or another, you could use
  the [Iris LaTeX macros](tex/iris.sty) for typesetting the various Iris
  connectives.
