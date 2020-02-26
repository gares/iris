# Iris Proof Guide

This work-in-progress document serves to explain how Iris proofs are typically
carried out in Coq: what are the common patterns and conventions, what are the
common pitfalls.  This complements the tactic documentation for the
[proof mode](./proof_mode.md) and [HeapLang](./heap_lang.md).

## Order of `Requires`

In Coq, declarations in modules imported later may override the
previous definition. Therefore, in order to make sure the most
relevant declarations and notations always take priority, we recommend
importing dependencies from the furthest to the closest.

In particular, when importing Iris, Stdpp and Coq stdlib modules, we
recommend importing in the following order:
- Coq
- stdpp
- iris.bi
- iris.proofmode
- iris.algebra
- iris.base_logic
- iris.program_logic
- iris.heap_lang

## Combinators for functors

In Iris, the type of propositions [iProp] is described by the solution to the
recursive domain equation:

```
iProp ≅ uPred (F (iProp))
```

Here, `F` is a user-chosen locally contractive bifunctor from COFEs to unital
Camaras (a step-indexed generalization of unital resource algebras). To make it
convenient to construct such functors out of smaller pieces, we provide a number
of abstractions:

- [`cFunctor`](theories/algebra/ofe.v): bifunctors from COFEs to OFEs.
- [`rFunctor`](theories/algebra/cmra.v): bifunctors from COFEs to cameras.
- [`urFunctor`](theories/algebra/cmra.v): bifunctors from COFEs to unital
  cameras.

Besides, there are the classes `cFunctorContractive`, `rFunctorContractive`, and
`urFunctorContractive` which describe the subset of the above functors that
are contractive.

To compose these functors, we provide a number of combinators, e.g.:

- `constCF (A : ofeT) : cFunctor           := λ (B,B⁻), A `
- `idCF : cFunctor                         := λ (B,B⁻), B`
- `prodCF (F1 F2 : cFunctor) : cFunctor    := λ (B,B⁻), F1 (B,B⁻) * F2 (B,B⁻)`
- `ofe_morCF (F1 F2 : cFunctor) : cFunctor := λ (B,B⁻), F1 (B⁻,B) -n> F2 (B,B⁻)`
- `laterCF (F : cFunctor) : cFunctor       := λ (B,B⁻), later (F (B,B⁻))`
- `agreeRF (F : cFunctor) : rFunctor       := λ (B,B⁻), agree (F (B,B⁻))`
- `gmapURF K (F : rFunctor) : urFunctor    := λ (B,B⁻), gmap K (F (B,B⁻))`

Using these combinators, one can easily construct bigger functors in point-free
style, e.g:

```
F := gmapURF K (agreeRF (prodCF (constCF natC) (laterCF idCF)))
```

which effectively defines `F := λ (B,B⁻), gmap K (agree (nat * later B))`.

Furthermore, for functors written using these combinators like the functor `F`
above, Coq can automatically `urFunctorContractive F`.

To make it a little bit more convenient to write down such functors, we make
the constant functors (`constCF`, `constRF`, and `constURF`) a coercion, and
provide the usual notation for products, etc. So the above functor can be
written as follows (which is similar to the effective definition of `F` above):

```
F := gmapURF K (agreeRF (natC * ▶ ∙))
```

## Resource algebra management

When using ghost state in Iris, you have to make sure that the resource algebras
you need are actually available.  Every Iris proof is carried out using a
universally quantified list `Σ: gFunctors` defining which resource algebras are
available.  The `Σ` is the *global* list of resources that the entire proof can
use.  We keep the `Σ` universally quantified to enable composition of proofs.

You can think of this as a list of resource algebras, though in reality it is a
list of locally contractive functors from COFEs to Cameras.  This list is used
to define the parameter `F` of Iris mentioned in the previous section. The
formal side of this is described in §7.4 of
[The Iris Documentation](http://plv.mpi-sws.org/iris/appendix-3.1.pdf); here we
describe the user-side Coq aspects of this approach.

The assumptions that an Iris proof makes are collected in a type class called
`somethingG`.  The most common kind of assumptions is `inG`, which says that a
particular resource algebra is available for ghost state.  For example, in the
[one-shot example](tests/one_shot.v):
```
Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.
```
The `:>` means that the projection `one_shot_inG` is automatically registered as
an instance for type-class resolution.  If you need several resource algebras,
just add more `inG` fields.  If you are using another module as part of yours,
add a field like `one_shot_other :> otherG Σ`.

Having defined the type class, we need to provide a way to instantiate it.  This
is an important step, as not every resource algebra can actually be used: if
your resource algebra refers to `Σ`, the definition becomes recursive.  That is
actually legal under some conditions (which is why the global list `Σ` contains
functors and not just resource algebras), but for the purpose of this guide we
will ignore that case.  We have to define a list that contains all the resource
algebras we need:
```
Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
```
This time, there is no `Σ` in the context, so we cannot accidentally introduce a
bad dependency.  If you are using another module as part of yours, add their
`somethingΣ` to yours, as in `#[GFunctor one_shotR; somethingΣ]`.  (The
`#[F1; F2; ...]` syntax *appends* the functor lists `F1`, `F2`, ... to each
other; together with a coercion from a single functor to a singleton list, this
means lists can be nested arbitrarily.)

Now we can define the one and only instance that our type class will ever need:
```
Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.
```
The `subG` assumption here says that the list `one_shotΣ` is a sublist of the
global list `Σ`.  Typically, this should be the only assumption your instance
needs, showing that the assumptions of the module (and all the modules it
uses internally) can trivially be satisfied by picking the right `Σ`.

Now you can add `one_shotG` as an assumption to all your module definitions and
proofs.  We typically use a section for this:
```
Section proof.
Context `{!heapG Σ, !one_shotG Σ}.
```
Notice that besides our own assumptions `one_shotG`, we also assume `heapG`,
which are assumptions that every HeapLang proof makes (they are related to
defining the `↦` connective as well as the basic Iris infrastructure for
invariants and WP).  For this purpose, `heapG` contains not only assumptions
about `Σ`, it also contains some ghost names to refer to particular ghost state
(see "global ghost state instances" below).

The backtic (`` ` ``) is used to make anonymous assumptions and to automatically
generalize the `Σ`.  When adding assumptions with backtic, you should most of
the time also add a `!` in front of every assumption.  If you do not then Coq
will also automatically generalize all indices of type-classes that you are
assuming.  This can easily lead to making more assumptions than you are aware
of, and often it leads to duplicate assumptions which breaks type class
resolutions.

### Obtaining a closed proof

To obtain a closed Iris proof, i.e., a proof that does not make assumptions like
`inG`, you have to assemble a list of functors of all the involved modules,
and if your proof relies on some singleton (most do, at least indirectly; also
see the next section), you have to call the respective initialization or
adequacy lemma.  [For example](tests/one_shot.v):
```
Section client.
  Context `{!heapG Σ, !one_shotG Σ, !spawnG Σ}.

  Lemma client_safe : WP client {{ _, True }}%I.
  (* ... *)
End client.

(** Assemble all functors needed by the [client_safe] proof. *)
Definition clientΣ : gFunctors := #[ heapΣ; one_shotΣ; spawnΣ ].

(** Apply [heap_adequacy] with this list of all functors. *)
Lemma client_adequate σ : adequate NotStuck client σ (λ _ _, True).
Proof. apply (heap_adequacy clientΣ)=> ?. apply client_safe. Qed.
```

### Advanced topic: Ghost state singletons

Some Iris modules involve a form of "global state".  For example, defining the
`↦` for HeapLang involves a piece of ghost state that matches the current
physical heap.  The `gname` of that ghost state must be picked once when the
proof starts, and then globally known everywhere.  Hence it is added to
`gen_heapG`, the type class for the generalized heap module:
```
Class gen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_inG :> inG Σ (authR (gen_heapUR L V));
  gen_heap_name : gname
}.
```

Such modules always need some kind of "initialization" to create an instance
of their type class.  For example, the initialization for `heapG` is happening
as part of [`heap_adequacy`](theories/heap_lang/adequacy.v); this in turn uses
the initialization lemma for `gen_heapG` from
[`gen_heap_init`](theories/base_logic/lib/gen_heap.v):
```
Lemma gen_heap_init `{gen_heapPreG L V Σ} σ :
  (|==> ∃ _ : gen_heapG L V Σ, gen_heap_ctx σ)%I.
```
These lemmas themselves only make assumptions the way normal modules (those
without global state) do, which are typically collected in a `somethingPreG`
type class (such as `gen_heapPreG`):
```
Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V))
}.
```
Just like in the normal case, `somethingPreG` type classes have an `Instance`
showing that a `subG` is enough to instantiate them:
```
Instance subG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.
```
The initialization lemma then shows that the `somethingPreG` type class is
enough to create an instance of the main `somethingG` class *below a view
shift*.  This is written with an existential quantifier in the lemma because the
statement after the view shift (`gen_heap_ctx σ` in this case) depends on having
an instance of `gen_heapG` in the context.

Given that these global ghost state instances are singletons, they must be
assumed explicitly everywhere.  Bundling `heapG` in a module type class like
`one_shotG` would lose track of the fact that there exists just one `heapG`
instance that is shared by everyone.

### Advanced topic: Additional module assumptions

Some modules need additional assumptions.  For example, the STS module is
parameterized by an STS and assumes that the STS state space is inhabited:
```
Class stsG Σ (sts : stsT) := {
  sts_inG :> inG Σ (stsR sts);
  sts_inhabited :> Inhabited (sts.state sts);
}.
```
In this rather exceptional case, the `Instance` for this class has more than
just a `subG` assumption:
```
Instance subG_stsΣ Σ sts :
  subG (stsΣ sts) Σ → Inhabited (sts.state sts) → stsG Σ sts.
```
If users of this module follow the pattern described above, their own type class
instance will check these additional assumption.  But this is one more reason
why it is important for every module to have an instance for its `somethingG`:
to make sure that it does not accidentally make more assumptions than it intends
to.

Another subtle detail here is that the `subG` assumption comes first in
`subG_stsΣ`, i.e., it appears before the `Inhabited`.  This is important because
otherwise, `sts_inhabited` and `subG_stsΣ` form an instance cycle that makes
type class search diverge.

## Canonical structures and type classes

In Iris, we use both canonical structures and type classes, and some careful
tweaking is necessary to make the two work together properly.  The details of
this still need to be written up properly, but here is some background material:

* [Type Classes for Mathematics in Type Theory](http://www.eelis.net/research/math-classes/mscs.pdf)
* [Canonical Structures for the working Coq user](https://hal.inria.fr/hal-00816703v1/document)

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
notations and their subexpressions.  For instance, to disambiguate `(⊢@{ PROP
})` and `(⊢@{ PROP } P)`, Coq must factor out a nonterminal for `⊢@{ PROP }`,
but it can only do so if all occurrences of `⊢@{ PROP }` agree on the
precedences for all subexpressions. This also requires using the same
tokenization in all cases, i.e., the notation has to consistently be declared as
`(⊢@{` or `('⊢@{'`, but not a mixture of the two. The latter form of using
explicit tokenization with `'` is preferred to avoid relying on Coq's default.

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
