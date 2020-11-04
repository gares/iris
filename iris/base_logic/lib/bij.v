(** Propositions for reasoning about monotone partial bijections.

This library provides two propositions [bij_own_auth γ L] and [bij_own_elem γ a b], where [L]
is a bijection between types [A] and [B] represented by a set of associations
[gset (A*B)]. The idea is that [bij_own_auth γ L] is an authoritative bijection [L]
while [bij_own_elem γ a b] is a persistent resource saying [L] associates a and b.

The main use case is in a logical relation-based proof where [L] maintains the
association between locations [A] in one execution and [B] in another (perhaps
of different types, if the logical relation relates two different semantics).

The association [L] is always bijective, so that if [a] is mapped to [b], there
should be no other mappings for either [a] or [b]; the [bij_own_extend] update
theorem enforces that new mappings respect this property, and [bij_own_elem_agree]
allows the user to exploit bijectivity. The bijection grows monotonically, so
that the set of associations only grows; this is captured by the persistence of
[bij_own_elem].

This library is a logical, ownership-based wrapper around bij_view.v. *)

From iris.algebra Require Import view gset lib.bij_view.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

Section bij.
  Context {A B : Type}.
  Context `{Countable A, Countable B}.

  (* The uCMRA we need. *)
  Class bijG Σ :=
    BijG { bijG_inG :> inG Σ (bij_viewR A B); }.

  Definition bijΣ : gFunctors := #[ GFunctor (bij_viewR A B) ].
  Global Instance subG_bijΣ Σ : subG bijΣ Σ → bijG Σ.
  Proof. solve_inG. Qed.

  Context `{!bijG Σ}.
  Implicit Types (L: gsetO (A * B)).
  Implicit Types (a:A) (b:B).

  Definition bij_own_auth_def γ L : iProp Σ := own γ (bij_auth L ⋅ bij_subrel L).
  Definition bij_own_auth_aux : seal (@bij_own_auth_def). Proof. by eexists. Qed.
  Definition bij_own_auth := unseal bij_own_auth_aux.
  Definition bij_own_auth_eq : @bij_own_auth = @bij_own_auth_def := seal_eq bij_own_auth_aux.

  Definition bij_own_elem_def γ a b: iProp Σ := own γ (bij_elem a b).
  Definition bij_own_elem_aux : seal (@bij_own_elem_def). Proof. by eexists. Qed.
  Definition bij_own_elem := unseal bij_own_elem_aux.
  Definition bij_own_elem_eq : @bij_own_elem = @bij_own_elem_def := seal_eq bij_own_elem_aux.

  Local Ltac unseal :=
    rewrite ?bij_own_auth_eq /bij_own_auth_def ?bij_own_elem_eq /bij_own_elem_def.

  Global Instance bij_own_auth_timeless γ L : Timeless (bij_own_auth γ L).
  Proof. unseal. apply _. Qed.

  Global Instance bij_own_elem_timeless γ a b : Timeless (bij_own_elem γ a b).
  Proof. unseal. apply _. Qed.

  Global Instance bij_own_elem_persistent γ a b : Persistent (bij_own_elem γ a b).
  Proof. unseal. apply _. Qed.

  Local Lemma bij_own_subrel_to_big_sepS γ L :
    own γ (bij_subrel L) -∗ [∗ set] ab ∈ L, own γ (bij_elem ab.1 ab.2).
  Proof.
    induction L as [|[a b] L] using set_ind_L.
    - rewrite big_sepS_empty. by iIntros "_".
    - rewrite bij_subrel_insert own_op.
      rewrite big_sepS_insert //=.
      rewrite IHL //.
  Qed.

  Lemma bij_own_alloc L :
    gset_bijective L →
    ⊢ |==> ∃ γ, bij_own_auth γ L ∗ [∗ set] ab ∈ L, bij_own_elem γ ab.1 ab.2.
  Proof.
    unseal.
    intros Hbij.
    iMod (own_alloc (bij_auth L ⋅ bij_subrel L)) as (γ) "[Hauth #Hsub]".
    { apply bij_both_subrel_valid; auto. }
    iModIntro. iExists γ.
    rewrite own_op. iFrame "Hsub ∗".
    iApply bij_own_subrel_to_big_sepS; auto.
  Qed.

  Lemma bij_own_alloc_empty : ⊢ |==> ∃ γ, bij_own_auth γ ∅.
  Proof.
    iMod (bij_own_alloc ∅) as (γ) "[Hauth _]";
      eauto using gset_bijective_empty.
  Qed.

  Lemma bij_own_bijective γ L :
    bij_own_auth γ L -∗ ⌜gset_bijective L⌝.
  Proof.
    unseal.
    rewrite own_op.
    iIntros "[Hauth _]".
    iDestruct (own_valid with "Hauth") as %?%bij_auth_valid; done.
  Qed.

  Lemma bij_own_elem_of γ L a b :
    (a, b) ∈ L →
    bij_own_auth γ L -∗ bij_own_elem γ a b.
  Proof.
    unseal.
    iIntros (Hel) "[_ Hfrag]".
    iDestruct (bij_own_subrel_to_big_sepS with "Hfrag") as "Hels".
    iDestruct (big_sepS_elem_of _ _ _ Hel with "Hels") as "$".
  Qed.

  Lemma bij_own_extend γ L a b :
    (∀ y, (a, y) ∉ L) → (∀ x, (x, b) ∉ L) →
    bij_own_auth γ L ==∗
    bij_own_auth γ ({[(a, b)]} ∪ L) ∗ bij_own_elem γ a b.
  Proof.
    unseal.
    iIntros (Ha Hb) "[HL Hfrag]".
    rewrite own_op.
    iMod (own_update with "HL") as "HL".
    { apply (bij_auth_extend a b); eauto. }
    iModIntro.
    iDestruct "HL" as "[$ #Hsub]".
    iFrame "Hsub".
    rewrite bij_subrel_insert own_op; iFrame "#∗".
  Qed.

  Lemma bij_own_extend_internal γ L a b :
    (∀ y, bij_own_elem γ a y -∗ False) -∗
    (∀ x, bij_own_elem γ x b -∗ False) -∗
    bij_own_auth γ L ==∗
    bij_own_auth γ ({[(a, b)]} ∪ L) ∗ bij_own_elem γ a b.
  Proof.
    iIntros "Ha Hb HL".
    iAssert (⌜∀ y, (a, y) ∉ L⌝)%I as %Ha.
    { iIntros (y Hel).
      iApply ("Ha" $! y).
      iApply (bij_own_elem_of with "HL"); eauto. }
    iAssert (⌜∀ x, (x, b) ∉ L⌝)%I as %Hb.
    { iIntros (x Hel).
      iApply ("Hb" $! x).
      iApply (bij_own_elem_of with "HL"); eauto. }
    iApply (bij_own_extend with "HL"); eauto.
  Qed.

  Lemma bij_own_extend' γ L a b :
    ¬(∃ y, (a, y) ∈ L) → ¬(∃ x, (x, b) ∈ L) →
    bij_own_auth γ L ==∗
    bij_own_auth γ ({[(a, b)]} ∪ L) ∗ bij_own_elem γ a b.
  Proof.
    intros.
    iApply bij_own_extend; naive_solver.
  Qed.

  Lemma bij_own_elem_agree γ L a a' b b' :
    bij_own_elem γ a b -∗ bij_own_elem γ a' b' -∗
    ⌜a = a' ↔ b = b'⌝.
  Proof.
    unseal.
    iIntros "Hel1 Hel2".
    iDestruct (own_valid_2 with "Hel1 Hel2") as %?%bij_elem_agree.
    auto.
  Qed.
End bij.

Arguments bijG A B {_ _ _ _} _ : assert.
Arguments bijΣ A B {_ _ _ _} : assert.
