(** RA for monotone partial bijections.

This RA is a view where the authoritative element is a partial bijection between
types [A] and [B] and the fragments are subrels of the bijection. The data for
the bijection is represented as a set of pairs [A*B], and the view relation
enforces when an authoritative element is valid it is a bijection (that is, it
is deterministic as a function from [A → option B] and [B → option A]).

The fragments compose by set union, which means that fragments are their own
core, ownership of a fragment is persistent, and the authoritative element can
only grow (in that it can only map more pairs (a,b)). *)

(** view needs to be exported for the canonical instances *)
From iris.algebra Require Export view gset.
From iris.algebra Require Import updates.
From iris.prelude Require Import options.

Section partial_bijection.
  Context `{Countable A, Countable B}.
  Implicit Types (a : A) (b : B).

  (** [gset_bijective] states that for a graph [L] of (a, b) pairs, [L] maps
  from [A] to [B] and back deterministically. The key property characterizing
  [gset_bijective] is [gset_bijective_eq_iff]. *)
  Definition gset_bijective (L : gset (A * B)) :=
    ∀ a b, (a, b) ∈ L →
    (∀ b', (a, b') ∈ L → b' = b) ∧ (∀ a', (a', b) ∈ L → a' = a).

  (* Properties of [gset_bijective]. *)
  Lemma gset_bijective_empty : gset_bijective (∅ : gset (A * B)).
  Proof. by intros ?? []%not_elem_of_empty. Qed.

  (* a bijective graph [L] can be extended with a new mapping [(a,b)] as long as
  neither [a] nor [b] is currently mapped to anything. *)
  Lemma gset_bijective_extend L a b :
    gset_bijective L →
    (∀ b', (a, b') ∉ L) →
    (∀ a', (a', b) ∉ L) →
    gset_bijective ({[(a, b)]} ∪ L).
  Proof. rewrite /gset_bijective. set_solver. Qed.

  Lemma gset_bijective_eq_iff L (a1 a2 : A) (b1 b2 : B) :
    gset_bijective L →
    (a1, b1) ∈ L →
    (a2, b2) ∈ L →
    a1 = a2 ↔ b1 = b2.
  Proof. rewrite /gset_bijective. set_solver. Qed.

  Lemma gset_bijective_pair a1 b1 a2 b2 :
    gset_bijective {[(a1, b1); (a2, b2)]} →
    (a1 = a2 ↔ b1 = b2).
  Proof. rewrite /gset_bijective. set_solver. Qed.

  Lemma subseteq_gset_bijective L L' :
    gset_bijective L →
    L' ⊆ L →
    gset_bijective L'.
  Proof. rewrite /gset_bijective. set_solver. Qed.

End partial_bijection.

Section bij.
  Context `{Countable A, Countable B}.
  Implicit Types (bijL : gset (A * B)) (L : gsetUR (A * B)).

  Local Definition bij_view_rel_raw (n : nat) bijL L: Prop :=
    L ⊆ bijL ∧ gset_bijective bijL.

  Local Lemma bij_view_rel_raw_mono n1 n2 bijL1 bijL2 L1 L2 :
    bij_view_rel_raw n1 bijL1 L1 →
    bijL1 ≡{n2}≡ bijL2 →
    L2 ≼{n2} L1 →
    n2 ≤ n1 →
    bij_view_rel_raw n2 bijL2 L2.
  Proof.
    intros [??] <-%(discrete_iff _ _)%leibniz_equiv ?%gset_included _.
    split; [|done]. by trans L1.
  Qed.

  Local Lemma bij_view_rel_raw_valid n bijL L :
    bij_view_rel_raw n bijL L → ✓{n}L.
  Proof. by intros _. Qed.

  Local Lemma bij_view_rel_raw_unit n :
    ∃ bijL, bij_view_rel_raw n bijL ε.
  Proof. exists ∅. split; eauto using gset_bijective_empty. Qed.

  Canonical Structure bij_view_rel : view_rel (gsetO (A * B)) (gsetUR (A * B)) :=
    ViewRel bij_view_rel_raw
            bij_view_rel_raw_mono bij_view_rel_raw_valid bij_view_rel_raw_unit.

  Global Instance bij_view_rel_discrete : ViewRelDiscrete bij_view_rel.
  Proof. intros n bijL L [??]. split; auto. Qed.

  Local Lemma bij_view_rel_iff n bijL L :
    bij_view_rel n bijL L ↔ L ⊆ bijL ∧ gset_bijective bijL.
  Proof. done. Qed.
End bij.

Definition bij_view A B `{Countable A, Countable B} :=
  view (bij_view_rel_raw (A:=A) (B:=B)).
Definition bij_viewO A B `{Countable A, Countable B} : ofeT :=
  viewO (bij_view_rel (A:=A) (B:=B)).
Definition bij_viewR A B `{Countable A, Countable B} : cmraT :=
  viewR (bij_view_rel (A:=A) (B:=B)).
Definition bij_viewUR A B `{Countable A, Countable B} : ucmraT :=
  viewUR (bij_view_rel (A:=A) (B:=B)).

Definition bij_auth `{Countable A, Countable B} (L : gset (A * B)) : bij_view A B :=
  ●V L ⋅ ◯V L.
Definition bij_elem `{Countable A, Countable B} (a : A) (b : B) : bij_view A B :=
  ◯V {[a, b]}.

Section bij.
  Context `{Countable A, Countable B}.
  Implicit Types (a:A) (b:B).
  Implicit Types (L : gset (A*B)).

  Global Instance bij_elem_core_id a b : CoreId (bij_elem a b).
  Proof. apply _. Qed.

  Lemma bij_auth_valid L : ✓ bij_auth L ↔ gset_bijective L.
  Proof.
    rewrite /bij_auth view_both_valid.
    setoid_rewrite bij_view_rel_iff.
    naive_solver eauto using O.
  Qed.

  Lemma bij_auth_valid_empty : ✓ bij_auth (A:=A) (B:=B) ∅.
  Proof. apply bij_auth_valid, gset_bijective_empty. Qed.

  Lemma bij_both_el_valid L a b :
    ✓ (bij_auth L ⋅ bij_elem a b) ↔ gset_bijective L ∧ (a, b) ∈ L.
  Proof.
    rewrite /bij_auth /bij_elem -assoc -view_frag_op view_both_valid.
    setoid_rewrite bij_view_rel_iff.
    set_solver by eauto using O.
  Qed.

  Lemma bij_elem_agree a1 b1 a2 b2 :
    ✓ (bij_elem a1 b1 ⋅ bij_elem a2 b2) → (a1 = a2 ↔ b1 = b2).
  Proof.
    rewrite /bij_elem -view_frag_op gset_op_union view_frag_valid.
    setoid_rewrite bij_view_rel_iff. intros. apply gset_bijective_pair.
    naive_solver eauto using subseteq_gset_bijective, O.
  Qed.

  Lemma bij_view_included L a b : (a,b) ∈ L → bij_elem a b ≼ bij_auth L.
  Proof.
    intros. etrans; [|apply cmra_included_r].
    apply view_frag_mono, gset_included. set_solver.
  Qed.

  Lemma bij_auth_extend L a b :
    (∀ b', (a, b') ∉ L) → (∀ a', (a', b) ∉ L) →
    bij_auth L ~~> bij_auth ({[(a, b)]} ∪ L).
  Proof.
    intros. apply view_update=> n bijL.
    rewrite !bij_view_rel_iff gset_op_union.
    set_solver by eauto using gset_bijective_extend.
  Qed.
End bij.
