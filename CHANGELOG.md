In this changelog, we document "large-ish" changes to Iris that affect even the
way the logic is used on paper.  We also document changes in the Coq
development; every API-breaking change should be listed, but not every new
lemma.

## Iris master

With this release, we dropped support for Coq 8.9.

We also split Iris into multiple opam packages: `coq-iris` no longer contains
HeapLang, which is now in a separate package `coq-iris-heap-lang`.

**Changes in `algebra`:**

* Rename `agree_op_inv'` to `to_agree_op_inv`,
  `agree_op_invL'` to `to_agree_op_inv_L`, and add
  `to_agree_op_invN`.
* Rename `auth_auth_frac_op_invL` to `auth_auth_frac_op_inv_L`,
  `excl_auth_agreeL` to `excl_auth_agree_L`,
  `frac_auth_agreeL` to `frac_auth_agree_L`, and
  `ufrac_auth_agreeL` to `ufrac_auth_agree_L`.
* Add constructions to define a camera through restriction of the validity predicate
  (`iso_cmra_mixin_restrict`) and through an isomorphism (`iso_cmra_mixin`).
* Add a `frac_agree` library which encapsulates `frac * agree A` for some OFE
  `A`, and provides some useful lemmas.
* Fix direction of `auth_auth_validN` to make it consistent with similar lemmas,
  e.g., `auth_auth_valid`. The direction is now `✓{n} (● a) ↔ ✓{n} a`.
* Rename `auth_both_valid` to `auth_both_valid_discrete` and
  `auth_both_frac_valid` to `auth_both_frac_valid_discrete`. The old name is
  used for new, stronger lemmas that do not assume discreteness.
* Add the view camera `view`, which generalizes the authoritative camera
  `auth` by being parameterized by a relation that relates the authoritative
  element with the fragments.
* Redefine the authoritative camera in terms of the view camera. As part of this
  change, we have removed lemmas that leaked implementation details. Hence, the
  only way to construct elements of `auth` is via the elements `●{q} a` and
  `◯ b`. The constructor `Auth`, and the projections `auth_auth_proj` and
  `auth_frag_proj` no longer exist. Lemmas that referred to these constructors
  have been removed, in particular: `auth_equivI`, `auth_validI`,
  `auth_included`, `auth_valid_discrete`, and `auth_both_op`.  For validity, use
  `auth_auth_valid*`, `auth_frag_valid*`, or `auth_both_valid*` instead.
* Rename `auth_update_core_id` into `auth_update_frac_alloc`.
* Add the camera of discardable fractions `dfrac`. This is a generalization of
  the normal fractional camera. See `theories/algebra/dfrac.v` for further information.
* Rename `cmra_monotone_valid` into `cmra_morphism_valid` (this rename was
  forgotten in !56).
* Add `gmap_view`, a camera providing a "view of a `gmap`". The authoritative
  element is any `gmap`; the fragment provides fractional ownership of a single
  key, including support for persistent read-only ownership through `dfrac`.
  See `theories/algebra/lib/gmap_view.v` for further information.
  NOTE: The API surface for `gmap_view` is experimental and subject to change.
* Move the `*_validI` and `*_equivI` lemmas to a new module, `base_logic.algebra`.
  That module is exported by `base_logic.base_logic` so it should usually be
  available everywhere without further changes.
* The authoritative fragment `✓ (◯ b : auth A)` is no longer definitionally
  equal to `✓ b`.
* Add `mnat_auth`, a wrapper for `auth max_nat`. The result is an authoritative
  `nat` where a fragment is a lower bound whose ownership is persistent.
* Change `*_valid` lemma statements involving fractions to use `Qp` addition and
  inequality instead of RA composition and validity (also in `base_logic` and
  the higher layers).

**Changes in `bi`:**

* Add big op lemmas `big_op{L,L2,M,M2,S}_intuitionistically_forall` and
  `big_sepL2_forall`, `big_sepMS_forall`, `big_sepMS_impl`, and `big_sepMS_dup`.
* Remove `bi.tactics` with tactics that predate the proofmode (and that have not
  been working properly for quite some time).
* Strengthen `persistent_sep_dup` to support propositions that are persistent
  and either affine or absorbing.

**Changes in `proofmode`:**

* The proofmode now preserves user-supplied names for existentials when using
  `iDestruct ... as (?) "..."`. This is backwards-incompatible if you were
  relying on the previous automatic names (which were always "H", possibly
  freshened). It also requires some changes if you were implementing `IntoExist`
  yourself, since the typeclass now forwards names. If your instance transforms
  one `IntoExist` into another, you can generally just forward the name from the
  premise.
* The proofmode also preserves user-supplied names in `iIntros`, for example
  with `iIntros (?)` and `iIntros "%"`, as described for destructing
  existentials above. As part of this change, it now uses a base name of `H` for
  pure facts rather than the previous default of `a`. This also requires some
  changes if you were implementing `FromForall`, in order to forward names.
* Make `iFrame` "less" smart w.r.t. clean up of modalities. It now consistently
  removes the modalities `<affine>`, `<absorbing>`, `<persistent>` and `□` only
  if the result after framing is `True` or `emp`. In particular, it no longer
  removes `<affine>` if the result after framing is affine, and it no longer
  removes `□` if the result after framing is intuitionistic.
* Allow framing below an `<affine>` modality if the hypothesis that is framed is
  affine. (Previously, framing below `<affine>` was only possible if the
  hypothesis that is framed resides in the intuitionistic context.)
* Remove the laws `pure_forall_2 : (∀ a, ⌜ φ a ⌝) ⊢ ⌜ ∀ a, φ a ⌝` from the BI
  interface and factor it into a type class `BiPureForall`.
* Add notation `¬ P` for `P → False` to `bi_scope`.

**Changes in `base_logic`:**

* Add a `ghost_var` library that provides (fractional) ownership of a ghost
  variable of arbitrary `Type`.
* Change type of some ghost state lemmas (mostly about allocation) to use `∗`
  instead of `∧` (consistent with our usual style).  This affects the following
  lemmas: `own_alloc_strong_dep`, `own_alloc_cofinite_dep`, `own_alloc_strong`,
  `own_alloc_cofinite`, `own_updateP`, `saved_anything_alloc_strong`,
  `saved_anything_alloc_cofinite`, `saved_prop_alloc_strong`,
  `saved_prop_alloc_cofinite`, `saved_pred_alloc_strong`,
  `saved_pred_alloc_cofinite`, `auth_alloc_strong`, `auth_alloc_cofinite`,
  `auth_alloc`.
* Change `uPred_mono` to only require inclusion at the smaller step-index.
* Put `iProp`/`iPreProp`-isomorphism into the `own` construction. This affects
  clients that define higher-order ghost state constructions. Concretely, when
  defining an `inG`, the functor no longer needs to be applied to `iPreProp`,
  but should be applied to `iProp`. This avoids clients from having to push
  through the `iProp`/`iPreProp`-isomorphism themselves, which is now handled
  once and for all by the `own` construction.
* Rename `gen_heap_ctx` to `gen_heap_interp`, since it is meant to be used in
  the state interpretation of WP and since `_ctx` is elsewhere used as a suffix
  indicating "this is a persistent assumption that clients should always have in
  their context". Likewise, rename `proph_map_ctx` to `proph_map_interp`.
* Move `uPred.prod_validI`, `uPred.option_validI`, and
  `uPred.discrete_fun_validI` to the new `base_logic.algebra` module. That
  module is exported by `base_logic.base_logic` so these names are now usually
  available everywhere, and no longer inside the `uPred` module.
* Add an `mnat` library on top of `mnat_auth` that supports ghost state which is
  an authoritative, monotonically-increasing `nat` with a proposition giving a
  persistent lower bound. See `base_logic.lib.mnat` for further details.
* Remove the `gen_heap` notations `l ↦ -` and `l ↦{q} -`. They were barely used
  and looked very confusing in context: `l ↦ - ∗ P` looks like a magic wand.
* Change `gen_inv_heap` notation `l ↦□ I` to `l ↦_I □`, so that `↦□` can be used
  by `gen_heap`.
* Strengthen `mapsto_valid_2` conclusion from `✓ (q1 + q2)%Qp` to
  `⌜✓ (q1 + q2)%Qp ∧ v1 = v2⌝`.
* Change `gen_heap_init` to also return ownership of the points-to facts for the
  initial heap.
* Rename `mapsto_mapsto_ne` to `mapsto_frac_ne`, and add a simpler
  `mapsto_ne` that does not require reasoning about fractions.

**Changes in `program_logic`:**

* `wp_strong_adequacy` now applies to an initial state with multiple
  threads instead of only a single thread. The derived adequacy lemmas
  are unchanged.

**Changes in `heap_lang`:**

* `wp_pures` now turns goals of the form `WP v {{ Φ }}` into `Φ v`.
* Fix `wp_bind` in case of a NOP (i.e., when the given expression pattern is
  already at the top level).

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# agree and L suffix renames
s/\bagree_op_inv'/to_agree_op_inv/g
s/\bagree_op_invL'/to_agree_op_inv_L/g
s/\bauth_auth_frac_op_invL\b/auth_auth_frac_op_inv_L/g
s/\b(excl|frac|ufrac)_auth_agreeL/\1_auth_agree_L/g
# auth_both_valid
s/\bauth_both_valid\b/auth_both_valid_discrete/g
s/\bauth_both_frac_valid\b/auth_both_frac_valid_discrete/g
# gen_heap_ctx and proph_map_ctx
s/\bgen_heap_ctx\b/gen_heap_interp/g
s/\bproph_map_ctx\b/proph_map_interp/g
# other gen_heap changes
s/\bmapsto_mapsto_ne\b/mapsto_frac_ne/g
EOF
```

## Iris 3.3.0 (released 2020-07-15)

This release does not have any outstanding highlights, but contains a large
number of improvements all over the board.  For instance:

* `heap_lang` now supports deallocation as well as better reasoning about
  "invariant locations" (locations that perpetually satisfy some Coq-level
  invariant).
* Invariants (`inv N P`) are more flexible, now also supporting splitting
  and merging of invariants with respect to separating conjunction.
* Performance of the proofmode for BIs constructed on top of other BIs (e.g.,
  `monPred`) was greatly improved, leading to up to 70% speedup in individual
  files. As part of this refactoring, the proofmode can now also be instantiated
  with entirely "logical" notion of BIs that do not have a (non-trivial) metric
  structure, and still support reasoning about ▷.
* The proof mode now provides experimental support for naming pure facts in
  intro patterns.  See
  [iris/string-ident](https://gitlab.mpi-sws.org/iris/string-ident) for details.
* Iris now provides official ASCII notation. We still recommend using the
  Unicode notation for better consistency and interoperability with other Iris
  libraries, but provide ASCII notation for when Unicode is not an option.
* We removed several coercions, fixing "ambiguous coercion path" warnings and
  solving some readability issues.
* Coq 8.10, 8.11, and 8.12 are newly supported by this release, and Coq 8.7 and
  8.8 are no longer supported.

Further details are given in the changelog below. We always first list the
potentially breaking changes, then (some of) the additions.

This release of Iris received contributions by Abel Nieto, Amin Timany, Dan
Frumin, Derek Dreyer, Dmitry Khalanskiy, Gregory Malecha, Jacques-Henri Jourdan,
Jonas Kastberg, Jules Jacobs, Matthieu Sozeau, Maxime Dénès, Michael Sammler,
Paolo G. Giarrusso, Ralf Jung, Robbert Krebbers, Simon Friis Vindum, Simon
Spies, and Tej Chajed.  Thanks a lot to everyone involved!

**Changes in `heap_lang`:**

* Remove global `Open Scope Z_scope` from `heap_lang.lang`, and leave it up to
  reverse dependencies if they want to `Open Scope Z_scope` or not.
* Fix all binary operators performing pointer arithmetic (instead of just the
  dedicated `OffsetOp` operator doing that).
* Rename `heap_lang.lifting` to `heap_lang.primitive_laws`. There now also
  exists `heap_lang.derived_laws`.
* Make lemma names for `fill` more consistent
  - Use the `_inv` suffix for the the backwards directions:
   `reducible_fill` → `reducible_fill_inv`,
   `reducible_no_obs_fill` → `reducible_no_obs_fill_inv`,
   `not_stuck_fill` → `not_stuck_fill_inv`.
  - Use the non-`_inv` names (that freed up) for the forwards directions:
   `reducible_fill`, `reducible_no_obs_fill`, `irreducible_fill_inv`.
* Remove namespace `N` from `is_lock`.

* Add support for deallocation of locations via the `Free` operation.
* Add a fraction to the heap_lang `array` assertion.
* Add `lib.array` module for deallocating, copying and cloning arrays.
* Add TWP (total weakest-pre) lemmas for arrays.
* Add a library for "invariant locations": heap locations that will not be
  deallocated (i.e., they are GC-managed) and satisfy some pure, Coq-level
  invariant.  See `iris.base_logic.lib.gen_inv_heap` for details.
* Add the ghost state for "invariant locations" to `heapG`.  This affects the
  statement of `heap_adequacy`, which is now responsible for initializing the
  "invariant locations" invariant.
* Add lemma `mapsto_mapsto_ne : ¬ ✓(q1 + q2)%Qp → l1 ↦{q1} v1 -∗ l2 ↦{q2} v2 -∗ ⌜l1 ≠ l2⌝`.
* Add lemma `is_lock_iff` and show that `is_lock` is contractive.

**Changes in `program_logic`:**

* In the axiomatization of ectx languages, replace the axiom of positivity of
  context composition with an axiom that says if `fill K e` takes a head step,
  then either `K` is the empty evaluation context or `e` is a value.

**Changes in the logic (`base_logic`, `bi`):**

* Rename some accessor-style lemmas to consistently use the suffix `_acc`
  instead of `_open`:
  `inv_open` → `inv_acc`, `inv_open_strong` → `inv_acc_strong`,
  `inv_open_timeless` → `inv_acc_timeless`, `na_inv_open` → `na_inv_acc`,
  `cinv_open` → `cinv_acc`, `cinv_open_strong` → `cinv_acc_strong`,
  `auth_open` → `auth_acc`, `sts_open` → `sts_acc`.
  To make this work, also rename `inv_acc` → `inv_alter`.
  (Most developments should be unaffected as the typical way to invoke these
  lemmas is through `iInv`, and that does not change.)
* Change `inv_iff`, `cinv_iff` and `na_inv_iff` to make order of arguments
  consistent and more convenient for `iApply`. They are now of the form
  `inv N P -∗ ▷ □ (P ↔ Q) -∗ inv N Q` and (similar for `na_inv_iff` and
  `cinv_iff`), following e.g., `inv_alter` and `wp_wand`.
* Rename `inv_sep_1` → `inv_split_1`, `inv_sep_2` → `inv_split_2`, and
  `inv_sep` → `inv_split` to be consistent with the naming convention in boxes.
* Update the strong variant of the accessor lemma for cancellable invariants to
  match that of regular invariants, where you can pick the mask at a later time.
  (The other part that makes it strong is that you get back the token for the
  invariant immediately, not just when the invariant is closed again.)
* Rename `iProp`/`iPreProp` to `iPropO`/`iPrePropO` since they are `ofeT`s.
  Introduce `iProp` for the `Type` carrier of `iPropO`.
* Flatten the BI hierarchy by merging the `bi` and `sbi` canonical structures.
  This gives significant performance benefits on developments that construct BIs
  from BIs (e.g., use `monPred`). For, example it gives a performance gain of 37%
  overall on lambdarust-weak, with improvements for individual files up to 72%,
  see Iris issue #303. The concrete changes are as follows:
  + The `sbi` canonical structure has been removed.
  + The `bi` canonical structure contains the later modality. It does not
    require the later modality to be contractive or to satisfy the Löb rule, so
    we provide a smart constructor `bi_later_mixin_id` to get the later axioms
    "for free" if later is defined to be the identity function.
  + There is a separate class `BiLöb`, and a "free" instance of that class if
    the later modality is contractive. A `BiLöb` instance is required for the
    `iLöb` tactic, and for timeless instances of implication and wand.
  + There is a separate type class `BiInternalEq` for BIs with a notion of
    internal equality (internal equality was part of `sbi`). An instance of this
    class is needed for the `iRewrite` tactic, and the various lemmas about
    internal equality.
  + The class `SbiEmbed` has been removed and been replaced by classes
    `BiEmbedLater` and `BiEmbedInternalEq`.
  + The class `BiPlainly` has been generalized to BIs without internal equality.
    As a consequence, there is a separate class `BiPropExt` for BIs with
    propositional extensionality (i.e., `■ (P ∗-∗ Q) ⊢ P ≡ Q`).
  + The class `BiEmbedPlainly` is a bi-entailment (i.e., `⎡■ P⎤ ⊣⊢ ■ ⎡P⎤`
    instead of `■ ⎡P⎤ ⊢ ⎡■ P⎤`) as it has been generalized to BIs without a
    internal equality. In the past, the left-to-right direction was obtained for
    "free" using the rules of internal equality.
* Remove coercion from `iProp` (and other MoSeL propositions) to `Prop`.
  Instead, use the new unary notation `⊢ P`, or `⊢@{PROP} P` if the proposition
  type cannot be inferred. This also means that `%I` should not be necessary any
  more when stating lemmas, as `P` above is automatically parsed in scope `%I`.
* Some improvements to the `bi/lib/core` construction:
  + Rename `coreP_wand` into `coreP_entails` since it does not involve wands.
  + Generalize `coreP_entails` to non-affine BIs, and prove more convenient
    version `coreP_entails'` for `coreP P` with `P` affine.
  + Add instance `coreP_affine P : Affine P → Affine (coreP P)` and
    lemma `coreP_wand P Q : <affine> ■ (P -∗ Q) -∗ coreP P -∗ coreP Q`.
* Remove notation for 3-mask step-taking updates, and made 2-mask notation less
  confusing by distinguishing it better from mask-changing updates.
  Old: `|={Eo,Ei}▷=> P`. New: `|={Eo}[Ei]▷=> P`.
  Here, `Eo` is the "outer mask" (used at the beginning and end) and `Ei` the
  "inner mask" (used around the ▷ in the middle).
  As part of this, the lemmas about the 3-mask variant were changed to be about
  the 2-mask variant instead, and `step_fupd_mask_mono` now also has a more
  consistent argument order for its masks.

* Add a counterexample showing that sufficiently powerful cancellable invariants
  with a linear token subvert the linearity guarantee (see
  `bi.lib.counterexmples` for details).
* Redefine invariants as "semantic invariants" so that they support
  splitting and other forms of weakening.
* Add lemmas `inv_combine` and `inv_combine_dup_l` for combining invariants.
* Add the type `siProp` of "plain" step-indexed propositions, together with
  basic proofmode support.
* New ASCII versions of Iris notations. These are marked parsing only and
  can be made available using `Require Import iris.bi.ascii`. The new
  notations are (notations marked [†] are disambiguated using notation scopes):
  - entailment: `|-` for `⊢` and `-|-` for `⊣⊢`
  - logic[†]: `->` for `→`, `/\\` for `∧`, `\\/` for `∨`, and `<->` for `↔`
  - quantifiers[†]: `forall` for `∀` and `exists` for `∃`
  - separation logic: `**` for `∗`, `-*` for `-∗`, and `*-*` for `∗-∗`
  - step indexing: `|>` for `▷`
  - modalities: `<#>` for `□` and `<except_0>` for `◇`
  - most derived notations can be computed from previous notations using the
    substitutions above, e.g. replace `∗` with `*` and `▷` with `|>`. Examples
    include the following:
    - `|={E1,E2}=* P` for `|={E1,E2}=∗`
    - `P ={E}=* Q` for `P ={E}=∗ Q`
    - `P ={E1,E2}=* Q` for `P ={E1,E2}=∗ Q`
    - `|={E1}[E2]|>=> Q` for `|={E1}[E2]▷=> Q`
    The full list can be found in [theories/bi/ascii.v](theories/bi/ascii.v),
    where the ASCII notations are defined in terms of the unicode notations.
* Add affine, absorbing, persistent and timeless instances for telescopes.
* Add a construction `bi_rtc` to create reflexive transitive closures of
  PROP-level binary relations.
* Slightly strengthen the lemmas `big_sepL_nil'`, `big_sepL2_nil'`,
  `big_sepM_nil'` `big_sepM2_empty'`, `big_sepS_empty'`, and `big_sepMS_empty'`.
  They now only require that the argument `P` is affine instead of the whole BI
  being affine.
* Add `big_sepL_insert_acc`, a variant of `big_sepL_lookup_acc` which allows
  updating the value.
* Add many missing `Proper`/non-expansiveness lemmas for big-ops.
* Add `big_*_insert_delete` lemmas to split a `<[i:=x]> m` map into `i` and the rest.
* Seal the definitions of `big_opS`, `big_opMS`, `big_opM` and `big_sepM2`
  to prevent undesired simplification.
* Fix `big_sepM2_fmap*` only working for `nat` keys.

**Changes in `proofmode`:**

* Make use of `notypeclasses refine` in the implementation of `iPoseProof` and
  `iAssumption`, see <https://gitlab.mpi-sws.org/iris/iris/merge_requests/329>.
  This has two consequences:
  1. Coq's "new" unification algorithm (the one in `refine`, not the "old" one
     in `apply`) is used more often by the proof mode tactics.
  2. Due to the use of `notypeclasses refine`, TC constraints are solved less
     eagerly, see <https://github.com/coq/coq/issues/6583>.
  In order to port your development, it is often needed to instantiate evars
  explicitly (since TC search is performed less eagerly), and in few cases it is
  needed to unfold definitions explicitly (due to new unification algorithm
  behaving differently).
* Strengthen the tactics `iDestruct`, `iPoseProof`, and `iAssert`:
  - They succeed in certain cases where they used to fail.
  - They keep certain hypotheses in the intuitionistic context, where they were
    moved to the spatial context before.
  The latter can lead to stronger proof mode contexts, and therefore to
  backwards incompatibility. This can usually be fixed by manually clearing some
  hypotheses. A more detailed description of the changes can be found in
  <https://gitlab.mpi-sws.org/iris/iris/merge_requests/341>.
* Remove the long-deprecated `cofeT` alias (for `ofeT`) and `dec_agree` RA (use
  `agree` instead).

* Add `auto` hint for `∗-∗`.
* Add new tactic `iStopProof` to turn the proof mode entailment into an ordinary
  Coq goal `big star of context ⊢ proof mode goal`.
* Add new introduction pattern `-# pat` that moves a hypothesis from the
  intuitionistic context to the spatial context.
* The tactic `iAssumption` also recognizes assumptions `⊢ P` in the Coq context.
* Better support for telescopes in the proof mode, i.e., all tactics should
  recognize and distribute telescopes now.
* The proof mode now supports names for pure facts in intro patterns. Support
  requires implementing `string_to_ident`. Without this tactic such patterns
  will fail. We provide one implementation using Ltac2 which works with Coq 8.11
  and can be installed with opam; see
  [iris/string-ident](https://gitlab.mpi-sws.org/iris/string-ident) for details.

**Changes in `algebra`:**

* Remove `Core` type class for defining the total core; it is now always
  defined in terms of the partial core. The only user of this type class was the
  STS RA.
* The functions `{o,r,ur}Functor_diag` are no longer coercions, and renamed into
  `{o,r,ur}Functor_apply` to better match their intent. This fixes "ambiguous
  coercion path" warnings.
* Rename `{o,r,ur}Functor_{ne,id,compose,contractive}` into
  `{o,r,ur}Functor_map_{ne,id,compose,contractive}`.
* Move derived camera constructions (`frac_auth` and `ufrac_auth`) to the folder
  `algebra/lib`.
* Rename `mnat` to `max_nat` and "box" it by creating a separate type for it.
* Move the RAs for `nat` and `positive` and the `mnat` RA into a separate
  module. They must now be imported from `From iris.algebra Require Import
  numbers`.
* Make names of `f_op`/`f_core` rewrite lemmas more consistent by always making
  `_core`/`_op` the suffix:
  `op_singleton` → `singleton_op`, `core_singleton` → `singleton_core`,
  `discrete_fun_op_singleton` → `discrete_fun_singleton_op`,
  `discrete_fun_core_singleton` → `discrete_fun_singleton_core`,
  `list_core_singletonM` → `list_singleton_core`,
  `list_op_singletonM` → `list_singleton_op`,
  `sts_op_auth_frag` → `sts_auth_frag_op`,
  `sts_op_auth_frag_up` → `sts_auth_frag_up_op`,
  `sts_op_frag` → `sts_frag_op`,
  `list_op_length` → `list_length_op`,
  `list_core_singletonM` → `list_singletonM_core`,
  `list_op_singletonM` → `list_singletonM_op`.
* All list "map singleton" lemmas consistently use `singletonM` in their name:
  `list_singleton_valid` → `list_singletonM_valid`,
  `list_singleton_core_id` → `list_singletonM_core_id`,
  `list_singleton_snoc` → `list_singletonM_snoc`,
  `list_singleton_updateP` → `list_singletonM_updateP`,
  `list_singleton_updateP'` → `list_singletonM_updateP'`,
  `list_singleton_update` → `list_singletonM_update`,
  `list_alloc_singleton_local_update` → `list_alloc_singletonM_local_update`.
* Remove `auth_both_op` and rename `auth_both_frac_op` into `auth_both_op`.
* Add lemma `singleton_included : {[ i := x ]} ≼ ({[ i := y ]} ↔ x ≡ y ∨ x ≼ y`,
  and rename existing asymmetric lemmas (with a singleton on just the LHS):
  `singleton_includedN` → `singleton_includedN_l`,
  `singleton_included` → `singleton_included_l`,
  `singleton_included_exclusive` → `singleton_included_exclusive_l`.

* Add notion `ofe_iso A B` that states that OFEs `A` and `B` are
  isomorphic. This is used in the COFE solver.
* Add `{o,r,ur}Functor_oFunctor_compose` for composition of functors.
* Add `pair_op_1` and `pair_op_2` to split a pair where one component is the unit.
* Add derived camera construction `excl_auth A` for `auth (option (excl A))`.
* Make lemma `Excl_included` a bi-implication.
* Make `auth_update_core_id` work with any fraction of the authoritative
  element.
* Add `min_nat`, an RA for natural numbers with `min` as the operation.
* Add many missing `Proper`/non-expansiveness lemmas for maps and lists.
* Add `list_singletonM_included` and `list_lookup_singletonM_{lt,gt}` lemmas
  about singletons in the list RA.
* Add `list_core_id'`, a stronger version of `list_core_id` which only talks
  about elements that are actually in the list.

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E '
# functor renames
s/\b(o|r|ur)Functor_(ne|id|compose|contractive)\b/\1Functor_map_\2/g
# singleton_included renames
s/\bsingleton_includedN\b/singleton_includedN_l/g
s/\bsingleton_included\b/singleton_included_l/g
s/\bsingleton_included_exclusive\b/singleton_included_exclusive_l/g
# f_op/f_core renames
s/\b(op|core)_singleton\b/singleton_\1/g
s/\bdiscrete_fun_(op|core)_singleton\b/discrete_fun_singleton_\1/g
s/\bsts_op_(auth_frag|auth_frag_up|frag)\b/sts_\1_op/g
s/\blist_(op|core)_singletonM\b/list_singletonM_\1/g
s/\blist_op_length\b/list_length_op/g
# list "singleton map" renames
s/\blist_singleton_valid\b/list_singletonM_valid/g
s/\blist_singleton_core_id\b/list_singletonM_core_id/g
s/\blist_singleton_snoc\b/list_singletonM_snoc/g
s/\blist_singleton_updateP\b/list_singletonM_updateP/g
s/\blist_singleton_update\b/list_singletonM_update/g
s/\blist_alloc_singleton_local_update\b/list_alloc_singletonM_local_update/g
# inv renames
s/\binv_sep(|_1|_2)\b/inv_split\1/g
s/\binv_acc\b/inv_alter/g
s/\binv_open(|_strong|_timeless)\b/inv_acc\1/g
s/\bcinv_open(|_strong)\b/cinv_acc\1/g
s/\b(na_inv|auth|sts)_open\b/\1_acc/g
# miscellaneous
s/\bauth_both_frac_op\b/auth_both_op/g
s/\bmnat\b/max_nat/g
s/\bcoreP_wand\b/coreP_entails/g
' $(find theories -name "*.v")
```

## Iris 3.2.0 (released 2019-08-29)

The highlight of this release is the completely re-engineered interactive proof
mode.  Not only did many tactics become more powerful; the entire proof mode can
now be used not just for Iris but also for other separation logics satisfying
the proof mode interface (e.g., [Iron] and [GPFSL]). Also see the
[accompanying paper][MoSeL].

[Iron]: https://iris-project.org/iron/
[GPFSL]: https://gitlab.mpi-sws.org/iris/gpfsl/
[MoSeL]: https://iris-project.org/mosel/

Beyond that, the Iris program logic gained the ability to reason about
potentially stuck programs, and a significantly strengthened adequacy theorem
that unifies the three previously separately presented theorems.  There are now
also Hoare triples for total program correctness (but with very limited support
for invariants) and logical atomicity.

And finally, our example language HeapLang was made more realistic
(Compare-and-set got replaced by compare-exchange and limited to only compare
values that can actually be compared atomically) and more powerful, with added
support for arrays and prophecy variables.

Further details are given in the changelog below.

This release of Iris received contributions by Aleš Bizjak, Amin Timany, Dan
Frumin, Glen Mével, Hai Dang, Hugo Herbelin, Jacques-Henri Jourdan, Jan Menz,
Jan-Oliver Kaiser, Jonas Kastberg Hinrichsen, Joseph Tassarotti, Mackie Loeffel,
Marianna Rapoport, Maxime Dénès, Michael Sammler, Paolo G. Giarrusso,
Pierre-Marie Pédrot, Ralf Jung, Robbert Krebbers, Rodolphe Lepigre, and Tej
Chajed. Thanks a lot to everyone involved!

**Changes in the theory of Iris itself:**

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

**Changes in heap_lang:**

* CAS (compare-and-set) got replaced by CmpXchg (compare-exchange).  The
  difference is that CmpXchg returns a pair consisting of the old value and a
  boolean indicating whether the comparison was successful and hence the
  exchange happened.  CAS can be obtained by simply projecting to the second
  component, but also providing the old value more closely models the primitive
  typically provided in systems languages (C, C++, Rust).
  The comparison by this operation also got weakened to be efficiently
  implementable: CmpXchg may only be used to compare "unboxed" values that can
  be represented in a single machine word. It is sufficient if one of the two
  compared values is unboxed.
* For consistency, the restrictions CmpXchg imposes on comparison also apply to
  the `=` binary operator. This also fixes the long-standing problem that that
  operator allowed compared closures with each other.
* Implement prophecy variables using the new support for "observations". The
  erasure theorem (showing that prophecy variables do not alter program
  behavior) can be found [in the iris/examples repository][prophecy-erasure].
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

[prophecy-erasure]: https://gitlab.mpi-sws.org/iris/examples/blob/3f33781fe6e19cfdb25259c8194d34403f1134d5/theories/logatom/proph_erasure.v

**Changes in Coq:**

* An all-new generalized proof mode that abstracts away from Iris!  Major new
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
* Rename `timelessP` → `timeless` (projection of the `Timeless` class)
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
* Lemma `prop_ext` works in both directions; its default direction is the
  opposite of what it used to be.
* Make direction of `f_op` rewrite lemmas more consistent: Flip `pair_op`,
  `Cinl_op`, `Cinr_op`, `cmra_morphism_op`, `cmra_morphism_pcore`,
  `cmra_morphism_core`.
* Rename lemmas `fupd_big_sep{L,M,S,MS}` into `big_sep{L,M,S,MS}_fupd` to be
  consistent with other such big op lemmas. Also add such lemmas for `bupd`.
* Rename `C` suffixes into `O` since we no longer use COFEs but OFEs. Also
  rename `ofe_fun` into `discrete_fun` and the corresponding notation `-c>` into
  `-d>`. The renaming can be automatically done using the following script
  (on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
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

**Changes in and extensions of the theory:**

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

**Changes in Coq:**

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
