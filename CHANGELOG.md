In this changelog, we document "large-ish" changes to Iris that affect even the
way the logic is used on paper.  We also mention some significant changes in the
Coq development, but not every API-breaking change is listed.  Changes marked
`[#]` still need to be ported to the Iris Documentation LaTeX file(s).

## Iris master

Changes in the theory of Iris itself:

* Change in the definition of WP, so that there is a fancy update between
  the quantification over the next states and the later modality. This makes it
  possible to prove more powerful lifting lemmas: The new versions feature an
  "update that takes a step".
* Add weakest preconditions for total program correctness.
* "(Potentially) stuck" weakest preconditions and the "plainly modality" are no
  longer considered experimental.
* Add the notion of an "observation" to the language interface, so that
  every reduction step can optionally be marked with an event, and an execution
  trace has a matching list of events.  Change WP so that it is told the entire
  future trace of observations from the beginning.
* The Löb rule is now a derived rule; it follows from later-intro, later
  being contractive and the fact that we can take fixpoints of contractive
  functions.
* Add atomic updates and logically atomic triples, including tactic support.
  See `heap_lang/lib/increment.v` for an example.
* Extend the state interpretation with a natural number that keeps track of
  the number of forked-off threads, and have a global fixed proposition that
  describes the postcondition of each forked-off thread (instead of it being
  `True`).
* A stronger adequacy statement for weakest preconditions that involves
  the final state, the post-condition of forked-off threads, and also applies if
  the main-thread has not terminated.
* The user-chosen functor used to instantiate the Iris logic now goes from
  COFEs to Cameras (it was OFEs to Cameras).

Changes in heap_lang:

* CAS (compare-and-set) got replaced by CmpXchg (compare-exchange).  The
  difference is that CmpXchg returns a pair consisting of the old value and a
  boolean indicating whether the comparison was successful and hence the
  exchange happened.  CAS can be obtained by simply projecting to the second
  component, but also providing the old value more closely models the primitive
  typically provided in systems languages (C, C++, Rust).
  The comparison by this operation also got weakened to be efficiently
  implementable: CmpXchg may only be used to compare "unboxed" values that can
  be represented in a single machine word.
* Implement prophecy variables using the new support for "observations".
* heap_lang now uses right-to-left evaluation order. This makes it
  significantly easier to write specifications of curried functions.
* heap_lang values are now injected in heap_lang expressions via a specific
  constructor of the expr inductive type. This simplifies much the tactical
  infrastructure around the language. In particular, this allow us to get rid
  the reflection mechanism that was needed for proving closedness, atomicity and
  "valueness" of a term. The price to pay is the addition of new
  "administrative" reductions in the operational semantics of the language.
* heap_lang now has support for allocating, accessing and reasoning about arrays
  (continuously allocated regions of memory).
* One can now assign "meta" data to heap_lang locations.
* For comparison operation (the binary operator and CmpXchg), all closures are
  "normalized" to the same.  This makes all closures indistinguishable from each
  other while remaining unqueal to anything else.  We also use the same
  "normalization" to make sure all prophecy variables seem equal to `()`.

Changes in Coq:

* An all-new generalized proof mode that abstracts away from Iris!  See
  <http://iris-project.org/mosel/> for the corresponding paper.  Major new
  features:
  - The proof mode can now be used with logics derived from Iris (like iGPS),
    with non-step-indexed logics and even with non-affine (i.e., linear) logics.
  - `iModIntro` is more flexible and more powerful, it now also subsumes
    `iNext` and `iAlways`.
  - General infrastructure for deriving a logic for monotone predicates over
    an existing logic (see the paper for more details).  
    Developments instantiating the proof mode typeclasses may need significant
    changes.  For developments just using the proof mode tactics, porting should
    not be too much effort.  Notable things to port are:
  - All the BI laws moved from the `uPred` module to the `bi` module.  For
    example, `uPred.later_equivI` became `bi.later_equivI`.
  - Big-ops are automatically imported, imports of `iris.base_logic.big_op` have
    to be removed.
  - The ⊢ notation can sometimes infer different (but convertible) terms when
    searching for the BI to use, which (due to Coq limitations) can lead to
    failing rewrites, in particular when rewriting at function types.
* The `iInv` tactic can now be used without the second argument (the name for
  the closing update).  It will then instead add the obligation to close the
  invariant to the goal.
* The new `iEval` tactic can be used to execute a simplification or rewriting
  tactic on some specific part(s) of the proofmode goal.
* Added support for defining derived connectives involving n-ary binders using
  telescopes.
* The proof mode now more consistently "prettifies" the goal after each tactic.
  Prettification also simplifies some BI connectives, like conditional
  modalities and telescope quantifiers.
* Improved pretty-printing of Iris connectives (in particular WP and fancy
  updates) when Coq has to line-wrap the output.  This goes hand-in-hand with an
  improved test suite that also tests pretty-printing.
* Added a `gmultiset` RA.
* Rename `timelessP` -> `timeless` (projection of the `Timeless` class)
* The CMRA axiom `cmra_extend` is now stated in `Type`, using `sigT` instead of
  in `Prop` using `exists`. This makes it possible to define the function space
  CMRA even for an infinite domain.
* Rename proof mode type classes for laters:
  - `IntoLaterN` → `MaybeIntoLaterN` (this one _may_ strip a later)
  - `IntoLaterN'` → `IntoLaterN` (this one _should_ strip a later)
  - `IntoLaterNEnv` → `MaybeIntoLaterNEnv`
  - `IntoLaterNEnvs` → `MaybeIntoLaterNEnvs`
* Rename:
  - `frag_auth_op` → `frac_auth_frag_op`
  - `cmra_opM_assoc` → `cmra_op_opM_assoc`
  - `cmra_opM_assoc_L` → `cmra_op_opM_assoc_L`
  - `cmra_opM_assoc'` → `cmra_opM_opM_assoc`
* `namespaces` has been moved to std++.
* Changed `IntoVal` to be directly usable for rewriting `e` into `of_val v`, and
  changed `AsVal` to be usable for rewriting via the `[v <-]` destruct pattern.
* `wp_fork` is now written in curried form.
* `PureExec`/`wp_pure` now supports taking multiple steps at once.
* A new tactic, `wp_pures`, executes as many pure steps as possible, excluding
  steps that would require unlocking subterms. Every impure wp_ tactic executes
  this tactic before doing anything else.
* Add `big_sepM_insert_acc`.
* Add big separating conjunctions that operate on pairs of lists (`big_sepL2`)
  and on pairs of maps (`big_sepM2`). In the former case the lists are required
  to have the same length, and in the latter case the maps are required to
  have the same domains.
* The `_strong` lemmas (e.g. `own_alloc_strong`) work for all infinite
  sets, instead of just for cofinite sets. The versions with cofinite
  sets have been renamed to use the `_cofinite` suffix.
* Remove locked value lambdas. The value scope notations `rec: f x := e` and
  `(λ: x, e)` no longer add a `locked`. Instead, we made the `wp_` tactics
  smarter to no longer unfold lambdas/recs that occur behind definitions.
* Export the fact that `iPreProp` is a COFE.
* The CMRA `auth` now can have fractional authoritative parts. So now `auth` has
  3 types of elements: the fractional authoritative `●{q} a`, the full
  authoritative `● a ≡ ●{1} a`, and the non-authoritative `◯ a`. Updates are
  only possible with the full authoritative element `● a`, while fractional
  authoritative elements have agreement: `✓ (●{p} a ⋅ ●{q} b) ⇒ a ≡ b`. As a
  consequence, `auth` is no longer a COFE and does not preserve Leibniz
  equality.
* Add a COFE construction (and functor) on dependent pairs `sigTO`, dual to
  `discrete_funO`.
* Rename in `auth`:
  - Use `auth_auth_proj`/`auth_frag_proj` for the projections of `auth`:
    `authoritative` → `auth_auth_proj` and `auth_own` → `auth_frag_proj`.
  - Use `auth_auth` and `auth_frag` for the injections into authoritative
    elements and non-authoritative elements respectively.
  - Lemmas for the projections and injections are renamed accordingly.
    For examples:
    + `authoritative_validN` → `auth_auth_proj_validN`
    + `auth_own_validN` → `auth_frag_proj_validN`
    + `auth_auth_valid` was not renamed because it was already used for the
      authoritative injection.
  - `auth_both_valid` → `auth_both_valid_2`
  - `auth_valid_discrete_2` → `auth_both_valid`
* Add the camera `ufrac` for unbounded fractions (i.e. without fractions that
  can be `> 1`) and the camera `ufrac_auth` for a variant of the authoritative
  fractional camera (`frac_auth`) with unbounded fractions.
* Changed `frac_auth` notation from `●!`/`◯!` to `●F`/`◯F`. sed script:
  `s/◯!/◯F/g; s/●!/●F/g;`.
* Rename `C` suffixes into `O` since we no longer use COFEs but OFEs. Also
  rename `ofe_fun` into `discrete_fun` and the corresponding notation `-c>` into
  `-d>`. The renaming can be automatically done using the following script (on
  macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i '
s/\bCofeMor/OfeMor/g;
s/\-c>/\-d>/g;
s/\bcFunctor/oFunctor/g;
s/\bCFunctor/OFunctor/g;
s/\b\%CF/\%OF/g;
s/\bconstCF/constOF/g;
s/\bidCF/idOF/g
s/\bdiscreteC/discreteO/g;
s/\bleibnizC/leibnizO/g;
s/\bunitC/unitO/g;
s/\bprodC/prodO/g;
s/\bsumC/sumO/g;
s/\bboolC/boolO/g;
s/\bnatC/natO/g;
s/\bpositiveC/positiveO/g;
s/\bNC/NO/g;
s/\bZC/ZO/g;
s/\boptionC/optionO/g;
s/\blaterC/laterO/g;
s/\bofe\_fun/discrete\_fun/g;
s/\bdiscrete\_funC/discrete\_funO/g;
s/\bofe\_morC/ofe\_morO/g;
s/\bsigC/sigO/g;
s/\buPredC/uPredO/g;
s/\bcsumC/csumO/g;
s/\bagreeC/agreeO/g;
s/\bauthC/authO/g;
s/\bnamespace_mapC/namespace\_mapO/g;
s/\bcmra\_ofeC/cmra\_ofeO/g;
s/\bucmra\_ofeC/ucmra\_ofeO/g;
s/\bexclC/exclO/g;
s/\bgmapC/gmapO/g;
s/\blistC/listO/g;
s/\bvecC/vecO/g;
s/\bgsetC/gsetO/g;
s/\bgset\_disjC/gset\_disjO/g;
s/\bcoPsetC/coPsetO/g;
s/\bgmultisetC/gmultisetO/g;
s/\bufracC/ufracO/g
s/\bfracC/fracO/g;
s/\bvalidityC/validityO/g;
s/\bbi\_ofeC/bi\_ofeO/g;
s/\bsbi\_ofeC/sbi\_ofeO/g;
s/\bmonPredC/monPredO/g;
s/\bstateC/stateO/g;
s/\bvalC/valO/g;
s/\bexprC/exprO/g;
s/\blocC/locO/g;
s/\bdec\_agreeC/dec\_agreeO/g;
s/\bgnameC/gnameO/g;
s/\bcoPset\_disjC/coPset\_disjO/g;
' $(find theories -name "*.v")
```

## Iris 3.1.0 (released 2017-12-19)

Changes in and extensions of the theory:

* Define `uPred` as a quotient on monotone predicates `M -> SProp`.
* Get rid of some primitive laws; they can be derived:
  `True ⊢ □ True` and `□ (P ∧ Q) ⊢ □ (P ∗ Q)`
* Camera morphisms have to be homomorphisms, not just monotone functions.
* Add a proof that `f` has a fixed point if `f^k` is contractive.
* Constructions for least and greatest fixed points over monotone predicates
  (defined in the logic of Iris using impredicative quantification).
* Add a proof of the inverse of `wp_bind`.
* [Experimental feature] Add new modality: ■ ("plainly").
* [Experimental feature] Support verifying code that might get stuck by
  distinguishing "non-stuck" vs. "(potentially) stuck" weakest
  preconditions. (See [Swasey et al., OOPSLA '17] for examples.) The non-stuck
  `WP e @ E {{ Φ }}` ensures that, as `e` runs, it does not get stuck. The stuck
  `WP e @ E ?{{ Φ }}` ensures that, as usual, all invariants are preserved while
  `e` runs, but it permits execution to get stuck. The former implies the
  latter. The full judgment is `WP e @ s; E {{ Φ }}`, where non-stuck WP uses
  *stuckness bit* `s = NotStuck` while stuck WP uses `s = MaybeStuck`.

Changes in Coq:

* Move the `prelude` folder to its own project:
  [coq-std++](https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp)
* Some extensions/improvements of heap_lang:
  - Improve handling of pure (non-state-dependent) reductions.
  - Add fetch-and-add (`FAA`) operation.
  - Add syntax for all Coq's binary operations on `Z`.
* Generalize `saved_prop` to let the user choose the location of the type-level
  later.  Rename the general form to `saved_anything`.  Provide `saved_prop` and
  `saved_pred` as special cases.
* Improved big operators:
  + They are no longer tied to cameras, but work on any monoid
  + The version of big operations over lists was redefined so that it enjoys
    more definitional equalities.
* Rename some things and change notation:
  - The unit of a camera: `empty` -> `unit`, `∅` -> `ε`
  - Disjointness: `⊥` -> `##`
  - A proof mode type class `IntoOp` -> `IsOp`
  - OFEs with all elements being discrete: `Discrete` -> `OfeDiscrete`
  - OFE elements whose equality is discrete: `Timeless` -> `Discrete`
  - Timeless propositions: `TimelessP` -> `Timeless`
  - Camera elements such that `core x = x`: `Persistent` -> `CoreId`
  - Persistent propositions: `PersistentP` -> `Persistent`
  - The persistent modality: `always` -> `persistently`
  - Adequacy for non-stuck weakestpre: `adequate_safe` -> `adequate_not_stuck`
  - Consistently SnakeCase identifiers:
    + `CMRAMixin` -> `CmraMixin`
    + `CMRAT` -> `CmraT`
    + `CMRATotal` -> `CmraTotal`
    + `CMRAMorphism` -> `CmraMorphism`
    + `CMRADiscrete` -> `CmraDiscrete`
    + `UCMRAMixin` -> `UcmraMixin`
    + `UCMRAT` -> `UcmraT`
    + `DRAMixin` -> `DraMixin`
    + `DRAT` -> `DraT`
    + `STS` -> `Sts`
  - Many lemmas also changed their name.  `always_*` became `persistently_*`,
    and furthermore: (the following list is not complete)
    + `impl_wand` -> `impl_wand_1` (it only involves one direction of the
      equivalent)
    + `always_impl_wand` -> `impl_wand`
    + `always_and_sep_l` -> `and_sep_l`
    + `always_and_sep_r` -> `and_sep_r`
    + `always_sep_dup` -> `sep_dup`
    + `wand_impl_always` -> `impl_wand_persistently` (additionally,
      the direction of this equivalence got swapped for consistency's sake)
    + `always_wand_impl` -> `persistently_impl_wand` (additionally, the
      direction of this equivalence got swapped for consistency's sake)
  The following `sed` snippet should get you most of the way (on macOS you will
  have to replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i 's/\bPersistentP\b/Persistent/g; s/\bTimelessP\b/Timeless/g; s/\bCMRADiscrete\b/CmraDiscrete/g; s/\bCMRAT\b/CmraT/g; s/\bCMRAMixin\b/CmraMixin/g; s/\bUCMRAT\b/UcmraT/g; s/\bUCMRAMixin\b/UcmraMixin/g; s/\bSTS\b/Sts/g' $(find -name "*.v")
```
* `PersistentL` and `TimelessL` (persistence and timelessness of lists of
  propositions) are replaces by `TCForall` from std++.
* Fix a bunch of consistency issues in the proof mode, and make it overall more
  usable.  In particular:
  - All proof mode tactics start the proof mode if necessary; `iStartProof` is
    no longer needed and should only be used for building custom proof mode
    tactics.
  - Change in the grammar of specialization patterns: `>[...]` -> `[> ...]`
  - Various new specification patterns for `done` and framing.
  - There is common machinery for symbolic execution of pure reductions. This
    is provided by the type classes `PureExec` and `IntoVal`.
  - There is a new connective `tc_opaque`, which can be used to make definitions
    opaque for type classes, and thus opaque for most tactics of the proof
    mode.
  - Define Many missing type class instances for distributing connectives.
  - Implement the tactics `iIntros (?)` and `iIntros "!#"` (i.e. `iAlways`)
    using type classes. This makes them more generic, e.g., `iIntros (?)` also
    works when the universal quantifier is below a modality, and `iAlways` also
    works for the plainness modality.  A breaking change, however, is that these
    tactics now no longer work when the universal quantifier or modality is
    behind a type class opaque definition.  Furthermore, this can change the
    name of anonymous identifiers introduced with the "%" pattern.
* Make `ofe_fun` dependently typed, subsuming `iprod`.  The latter got removed.
* Define the generic `fill` operation of the `ectxi_language` construct in terms
  of a left fold instead of a right fold. This gives rise to more definitional
  equalities.
* The language hierarchy (`language`, `ectx_language`, `ectxi_language`) is now
  fully formalized using canonical structures instead of using a mixture of
  type classes and canonical structures. Also, it now uses explicit mixins. The
  file `program_logic/ectxi_language` contains some documentation on how to
  setup Iris for your language.
* Restore the original, stronger notion of atomicity alongside the weaker
  notion. These are `Atomic a e` where the stuckness bit `s` indicates whether
  expression `e` is weakly (`a = WeaklyAtomic`) or strongly
  (`a = StronglyAtomic`) atomic.
* Various improvements to `solve_ndisj`.
* Use `Hint Mode` to prevent Coq from making arbitrary guesses in the presence
  of evars, which often led to divergence. There are a few places where type
  annotations are now needed.
* The rules `internal_eq_rewrite` and `internal_eq_rewrite_contractive` are now
  stated in the logic, i.e., they are `iApply`-friendly.

## Iris 3.0.0 (released 2017-01-11)

* There now is a deprecation process.  The modules `*.deprecated` contain
  deprecated notations and definitions that are provided for backwards
  compatibility and will be removed in a future version of Iris.
* View shifts are radically simplified to just internalize frame-preserving
  updates.  Weakestpre is defined inside the logic, and invariants and view
  shifts with masks are also coded up inside Iris.  Adequacy of weakestpre is
  proven in the logic. The old ownership of the entire physical state is
  replaced by a user-selected predicate over physical state that is maintained
  by weakestpre.
* Use OFEs instead of COFEs everywhere.  COFEs are only used for solving the
  recursive domain equation.  As a consequence, CMRAs no longer need a proof of
  completeness.  (The old `cofeT` is provided by `algebra.deprecated`.)
* Implement a new agreement construction.  Unlike the old one, this one
  preserves discreteness.  dec_agree is thus no longer needed and has been moved
  to algebra.deprecated.
* Renaming and moving things around: uPred and the rest of the base logic are in
  `base_logic`, while `program_logic` is for everything involving the general
  Iris notion of a language.
* Renaming in prelude.list: Rename `prefix_of` -> `prefix` and `suffix_of` ->
  `suffix` in lemma names, but keep notation ``l1 `prefix_of` l2`` and ``l1
  `suffix_of` l2``.  `` l1 `sublist` l2`` becomes ``l1 `sublist_of` l2``. Rename
  `contains` -> `submseteq` and change `` l1 `contains` l2`` to ``l1 ⊆+ l2``.
* Slightly weaker notion of atomicity: an expression is atomic if it reduces in
  one step to something that does not reduce further.
* Changed notation for embedding Coq assertions into Iris.  The new notation is
  ⌜φ⌝.  Also removed `=` and `⊥` from the Iris scope.  (The old notations are
  provided in `base_logic.deprecated`.)
* Up-closure of namespaces is now a notation (↑) instead of a coercion.
* With invariants and the physical state being handled in the logic, there is no
  longer any reason to demand the CMRA unit to be discrete.
* The language can now fork off multiple threads at once.
* Local Updates (for the authoritative monoid) are now a 4-way relation with
  syntax-directed lemmas proving them.

## Iris 2.0

* [heap_lang] No longer use dependent types for expressions.  Instead, values
  carry a proof of closedness.  Substitution, closedness and value-ness proofs
  are performed by computation after reflecting into a term langauge that knows
  about values and closed expressions.
* [program_logic/language] The language does not define its own "atomic"
  predicate.  Instead, atomicity is defined as reducing in one step to a value.
* [program_logic] Due to a lack of maintenance and usefulness, lifting lemmas
  for Hoare triples are removed.

## Iris 2.0-rc2

This version matches the final ICFP 2016 paper.

* [algebra] Make the core of an RA or CMRA a partial function.
* [program_logic/lifting] Lifting lemmas no longer round-trip through a
  user-chosen predicate to define the configurations we can reduce to; they
  directly relate to the operational semantics.  This is equivalent and
  much simpler to read.

## Iris 2.0-rc1

This is the Coq development and Iris Documentation as submitted to ICFP 2016.
