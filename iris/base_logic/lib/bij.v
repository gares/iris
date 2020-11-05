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
From iris.bi.lib Require Import fractional.
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

Definition bij_own_auth_def `{bijG A B Σ} (γ : gname)
  (q : Qp) (L : gset (A * B)) : iProp Σ := own γ (bij_auth q L).
Definition bij_own_auth_aux : seal (@bij_own_auth_def). Proof. by eexists. Qed.
Definition bij_own_auth := unseal bij_own_auth_aux.
Definition bij_own_auth_eq :
  @bij_own_auth = @bij_own_auth_def := seal_eq bij_own_auth_aux.
Arguments bij_own_auth {_ _ _ _ _ _ _ _}.

Definition bij_own_elem_def `{bijG A B Σ} (γ : gname)
  (a : A) (b : B) : iProp Σ := own γ (bij_elem a b).
Definition bij_own_elem_aux : seal (@bij_own_elem_def). Proof. by eexists. Qed.
Definition bij_own_elem := unseal bij_own_elem_aux.
Definition bij_own_elem_eq :
  @bij_own_elem = @bij_own_elem_def := seal_eq bij_own_elem_aux.
Arguments bij_own_elem {_ _ _ _ _ _ _ _}.

Section bij.
  Context `{bijG A B Σ}.
  Implicit Types (L : gset (A * B)) (a : A) (b : B).

  Global Instance bij_own_auth_timeless γ q L : Timeless (bij_own_auth γ q L).
  Proof. rewrite bij_own_auth_eq. apply _. Qed.
  Global Instance bij_own_elem_timeless γ a b : Timeless (bij_own_elem γ a b).
  Proof. rewrite bij_own_elem_eq. apply _. Qed.
  Global Instance bij_own_elem_persistent γ a b : Persistent (bij_own_elem γ a b).
  Proof. rewrite bij_own_elem_eq. apply _. Qed.

  Global Instance bij_own_auth_fractional γ L : Fractional (λ q, bij_own_auth γ q L).
  Proof. intros p q. rewrite bij_own_auth_eq -own_op bij_auth_frac_op //. Qed.
  Global Instance bij_own_auth_as_fractional γ q L :
    AsFractional (bij_own_auth γ q L) (λ q, bij_own_auth γ q L) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma bij_own_auth_agree γ q1 q2 L1 L2 :
    bij_own_auth γ q1 L1 -∗ bij_own_auth γ q2 L2 -∗
    ⌜✓ (q1 + q2)%Qp ∧ L1 = L2 ∧ gset_bijective L1⌝.
  Proof.
    rewrite bij_own_auth_eq. iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as %?%bij_auth_frac_op_valid.
  Qed.
  Lemma bij_own_auth_exclusive γ L1 L2 :
    bij_own_auth γ 1 L1 -∗ bij_own_auth γ 1 L2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (bij_own_auth_agree with "H1 H2") as %[[] _].
  Qed.

  Lemma bij_own_valid γ q L :
    bij_own_auth γ q L -∗ ⌜✓ q ∧ gset_bijective L⌝.
  Proof.
    rewrite bij_own_auth_eq. iIntros "Hauth".
    by iDestruct (own_valid with "Hauth") as %?%bij_auth_frac_valid.
  Qed.

  Lemma bij_own_elem_agree γ L a a' b b' :
    bij_own_elem γ a b -∗ bij_own_elem γ a' b' -∗
    ⌜a = a' ↔ b = b'⌝.
  Proof.
    rewrite bij_own_elem_eq. iIntros "Hel1 Hel2".
    by iDestruct (own_valid_2 with "Hel1 Hel2") as %?%bij_elem_agree.
  Qed.

  Lemma bij_get_elem γ q L a b :
    (a, b) ∈ L →
    bij_own_auth γ q L -∗ bij_own_elem γ a b.
  Proof.
    intros. rewrite bij_own_auth_eq bij_own_elem_eq.
    by apply own_mono, bij_view_included.
  Qed.
  Lemma bij_get_big_sepS_elem γ q L :
    bij_own_auth γ q L -∗ [∗ set] ab ∈ L, bij_own_elem γ ab.1 ab.2.
  Proof.
    iIntros "Hauth". iApply big_sepS_forall. iIntros ([a b] ?) "/=".
    by iApply bij_get_elem.
  Qed.

  Lemma bij_own_alloc L :
    gset_bijective L →
    ⊢ |==> ∃ γ, bij_own_auth γ 1 L ∗ [∗ set] ab ∈ L, bij_own_elem γ ab.1 ab.2.
  Proof.
    intro. iAssert (∃ γ, bij_own_auth γ 1 L)%I with "[>]" as (γ) "Hauth".
    { rewrite bij_own_auth_eq. iApply own_alloc. by apply bij_auth_valid. }
    iExists γ. iModIntro. iSplit; [done|]. by iApply bij_get_big_sepS_elem.
 Qed.
  Lemma bij_own_alloc_empty :
    ⊢ |==> ∃ γ, bij_own_auth γ 1 ∅.
  Proof. iMod (bij_own_alloc ∅) as (γ) "[Hauth _]"; by auto. Qed.

  Lemma bij_own_extend γ L a b :
    (∀ b', (a, b') ∉ L) → (∀ a', (a', b) ∉ L) →
    bij_own_auth γ 1 L ==∗ bij_own_auth γ 1 ({[(a, b)]} ∪ L) ∗ bij_own_elem γ a b.
  Proof.
    iIntros (??) "Hauth".
    iAssert (bij_own_auth γ 1 ({[a, b]} ∪ L)) with "[> Hauth]" as "Hauth".
    { rewrite bij_own_auth_eq. iApply (own_update with "Hauth").
      by apply bij_auth_extend. }
    iModIntro. iSplit; [done|]. iApply (bij_get_elem with "Hauth"). set_solver.
  Qed.

  Lemma bij_own_extend_internal γ L a b :
    (∀ b', bij_own_elem γ a b' -∗ False) -∗
    (∀ a', bij_own_elem γ a' b -∗ False) -∗
    bij_own_auth γ 1 L ==∗ bij_own_auth γ 1 ({[(a, b)]} ∪ L) ∗ bij_own_elem γ a b.
  Proof.
    iIntros "Ha Hb HL".
    iAssert ⌜∀ b', (a, b') ∉ L⌝%I as %?.
    { iIntros (b' ?). iApply ("Ha" $! b'). by iApply bij_get_elem. }
    iAssert ⌜∀ a', (a', b) ∉ L⌝%I as %?.
    { iIntros (a' ?). iApply ("Hb" $! a'). by iApply bij_get_elem. }
    by iApply (bij_own_extend with "HL").
  Qed.
End bij.
