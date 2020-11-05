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

From iris.algebra.lib Require Import bij_view.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

(* The uCMRA we need. *)
Class bijG A B `{Countable A, Countable B} Σ :=
  BijG { bijG_inG :> inG Σ (bij_viewR A B); }.

Definition bijΣ A B `{Countable A, Countable B}: gFunctors :=
  #[ GFunctor (bij_viewR A B) ].
Global Instance subG_bijΣ `{Countable A, Countable B} Σ :
  subG (bijΣ A B) Σ → bijG A B Σ.
Proof. solve_inG. Qed.

Section bij.
  Context `{bijG A B Σ}.
  Implicit Types (L: gsetO (A * B)).
  Implicit Types (a:A) (b:B).

  Definition bij_own_auth_def γ L : iProp Σ := own γ (bij_auth L).
  Definition bij_own_auth_aux : seal (@bij_own_auth_def). Proof. by eexists. Qed.
  Definition bij_own_auth := unseal bij_own_auth_aux.
  Definition bij_own_auth_eq :
    @bij_own_auth = @bij_own_auth_def := seal_eq bij_own_auth_aux.

  Definition bij_own_elem_def γ a b: iProp Σ := own γ (bij_elem a b).
  Definition bij_own_elem_aux : seal (@bij_own_elem_def). Proof. by eexists. Qed.
  Definition bij_own_elem := unseal bij_own_elem_aux.
  Definition bij_own_elem_eq :
    @bij_own_elem = @bij_own_elem_def := seal_eq bij_own_elem_aux.

  Global Instance bij_own_auth_timeless γ L : Timeless (bij_own_auth γ L).
  Proof. rewrite bij_own_auth_eq. apply _. Qed.

  Global Instance bij_own_elem_timeless γ a b : Timeless (bij_own_elem γ a b).
  Proof. rewrite bij_own_elem_eq. apply _. Qed.

  Global Instance bij_own_elem_persistent γ a b : Persistent (bij_own_elem γ a b).
  Proof. rewrite bij_own_elem_eq. apply _. Qed.

  Lemma bij_own_bijective γ L :
    bij_own_auth γ L -∗ ⌜gset_bijective L⌝.
  Proof.
    rewrite bij_own_auth_eq. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%bij_auth_valid; done.
  Qed.

  Lemma bij_own_elem_agree γ L a a' b b' :
    bij_own_elem γ a b -∗ bij_own_elem γ a' b' -∗
    ⌜a = a' ↔ b = b'⌝.
  Proof.
    rewrite bij_own_elem_eq. iIntros "Hel1 Hel2".
    by iDestruct (own_valid_2 with "Hel1 Hel2") as %?%bij_elem_agree.
  Qed.

  Lemma bij_get_elem γ L a b :
    (a, b) ∈ L →
    bij_own_auth γ L -∗ bij_own_elem γ a b.
  Proof.
    intros. rewrite bij_own_auth_eq bij_own_elem_eq.
    by apply own_mono, bij_view_included.
  Qed.
  Lemma bij_get_big_sepS_elem γ L :
    bij_own_auth γ L -∗ [∗ set] ab ∈ L, bij_own_elem γ ab.1 ab.2.
  Proof.
    iIntros "Hauth". iApply big_sepS_forall. iIntros ([a b] ?) "/=".
    by iApply bij_get_elem.
  Qed.

  Lemma bij_own_alloc L :
    gset_bijective L →
    ⊢ |==> ∃ γ, bij_own_auth γ L ∗ [∗ set] ab ∈ L, bij_own_elem γ ab.1 ab.2.
  Proof.
    intro. iAssert (∃ γ, bij_own_auth γ L)%I with "[>]" as (γ) "Hauth".
    { rewrite bij_own_auth_eq. iApply own_alloc. by apply bij_auth_valid. }
    iExists γ. iModIntro. iSplit; [done|]. by iApply bij_get_big_sepS_elem.
 Qed.
  Lemma bij_own_alloc_empty :
    ⊢ |==> ∃ γ, bij_own_auth γ ∅.
  Proof. iMod (bij_own_alloc ∅) as (γ) "[Hauth _]"; by auto. Qed.

  Lemma bij_own_extend γ L a b :
    (∀ b', (a, b') ∉ L) → (∀ a', (a', b) ∉ L) →
    bij_own_auth γ L ==∗ bij_own_auth γ ({[(a, b)]} ∪ L) ∗ bij_own_elem γ a b.
  Proof.
    iIntros (??) "Hauth".
    iAssert (bij_own_auth γ ({[a, b]} ∪ L)) with "[> Hauth]" as "Hauth".
    { rewrite bij_own_auth_eq. iApply (own_update with "Hauth").
      by apply bij_auth_extend. }
    iModIntro. iSplit; [done|]. iApply (bij_get_elem with "Hauth"). set_solver.
  Qed.

  Lemma bij_own_extend_internal γ L a b :
    (∀ b', bij_own_elem γ a b' -∗ False) -∗
    (∀ a', bij_own_elem γ a' b -∗ False) -∗
    bij_own_auth γ L ==∗ bij_own_auth γ ({[(a, b)]} ∪ L) ∗ bij_own_elem γ a b.
  Proof.
    iIntros "Ha Hb HL".
    iAssert ⌜∀ b', (a, b') ∉ L⌝%I as %?.
    { iIntros (b' ?). iApply ("Ha" $! b'). by iApply bij_get_elem. }
    iAssert ⌜∀ a', (a', b) ∉ L⌝%I as %?.
    { iIntros (a' ?). iApply ("Hb" $! a'). by iApply bij_get_elem. }
    by iApply (bij_own_extend with "HL").
  Qed.
End bij.
