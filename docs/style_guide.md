# Iris Style Guide

This document lays down syntactic conventions about how we usually write our
Iris proofs in Coq.  It is a work-in-progress.  This complements the tactic
documentation for the [proof mode](./proof_mode.md) and [HeapLang](./heap_lang.md) as
well as the [proof guide](./proof_guide.md).

## Implicit generalization

We often use the implicit generalization feature of Coq, triggered by a backtic:
`` `{!term A B}`` means that an implicit argument of type `term A B` is added,
and if any of the identifiers that are used here is not yet bound, it gets added
as well.  Usually, `term` will be some existing type class or similar, and we
use this syntax to also generalize over `A` and `B`; then the above is
equivalent to `{A B} {Hterm: term A B}`.  The `!` in front of the term disables
an even stronger form of generalization, where if `term` is a type class then
all missing arguments get implicitly generalized as well.  This is sometimes
useful, e.g. we can write `` `{Countable C}`` instead of `` `{!EqDecision C,
!Countable C}``.  However, generally it is more important to be aware of the
assumptions you are making, so implicit generalization without `!` should be
avoided.

## Type class resolution control

When you are writing a module that exports some Iris term for others to use
(e.g., `join_handle` in the [spawn module](theories/heap_lang/lib/spawn.v)), be
sure to mark these terms as opaque for type class search at the *end* of your
module (and outside any section):
```
Typeclasses Opaque join_handle.
```
This makes sure that the proof mode does not "look into" your definition when it
is used by clients.

## Notations

Notations starting with `(` or `{` should be left at their default level (`0`),
and inner subexpressions that are bracketed by delimiters should be left at
their default level (`200`).

Moreover, correct parsing of notations sometimes relies on Coq's automatic
left-factoring, which can require coordinating levels of certain "conflicting"
notations and their subexpressions. For instance, to disambiguate `(⊢@{ PROP })`
and `(⊢@{ PROP } P)`, Coq must factor out a nonterminal for `⊢@{ PROP }`, but it
can only do so if all occurrences of `⊢@{ PROP }` agree on the precedences for
all subexpressions.

For details, consult [the Coq manual](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#simple-factorization-rules).

## Naming conventions for variables/arguments/hypotheses

### small letters

* a : A = cmraT or ofeT
* b : B = cmraT or ofeT
* c
* d
* e : expr = expressions
* f = some generic function
* g = some generic function
* h : heap
* i
* j
* k
* l
* m : iGst = ghost state
* m* = prefix for option
* n
* o
* p
* q
* r : iRes = resources
* s = state (STSs)
* s = stuckness bits
* t
* u
* v : val = values of language
* w
* x
* y
* z 

### capital letters

* A : Type, cmraT or ofeT
* B : Type, cmraT or ofeT
* C
* D   
* E : coPset = Viewshift masks
* F = a functor
* G
* H = hypotheses
* I = indexing sets
* J
* K : ectx = evaluation contexts
* K = keys of a map
* L
* M = maps / global CMRA
* N : namespace
* O 
* P : uPred, iProp or Prop
* Q : uPred, iProp or Prop
* R : uPred, iProp or Prop
* S : set state = state sets in STSs
* T : set token = token sets in STSs
* U
* V : abstraction of value type in frame shift assertions
* W
* X : sets
* Y : sets
* Z : sets

### small greek letters

* γ : gname
* σ : state = state of language
* φ : interpretation of STS/Auth

### capital greek letters

* Φ : general predicate (over uPred, iProp or Prop)
* Ψ : general predicate (over uPred, iProp or Prop)

## Naming conventions for algebraic classes

### Suffixes

* O: OFEs
* R: cameras
* UR: unital cameras or resources algebras
* F: functors (can be combined with all of the above, e.g. OF is an OFE functor)
* G: global camera functor management (typeclass; see [proof\_guide.md](./proof_guide.md))
* I: bunched implication logic (of type `bi`)
* SI: step-indexed bunched implication logic (of type `sbi`)
* T: canonical structures for algebraic classes (for example ofeT for OFEs, cmraT for cameras)
* Σ: global camera functor management (`gFunctors`; see [proof\_guide.md](./proof_guide.md))
