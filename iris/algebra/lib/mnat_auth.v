From iris.algebra Require Export auth.
From iris.algebra Require Import numbers updates.
From iris.prelude Require Import options.

(** Authoritative CMRA for [max_nat]. The authoritative element is a
monotonically increasing [nat], while a fragment is a lower bound. *)

Definition mnat_auth   := auth max_natUR.
Definition mnat_authR  := authR max_natUR.
Definition mnat_authUR := authUR max_natUR.

(** [mnat_auth_auth] is the authoritative element. The definition includes the
fragment at the same value so that lemma [mnat_auth_included], which states that
[mnat_auth_frag n ≼ mnat_auth_auth q n], does not require a frame-preserving
update. *)
Definition mnat_auth_auth (q : Qp) (n : nat) : mnat_auth :=
  ●{q} MaxNat n ⋅ ◯ MaxNat n.
Definition mnat_auth_frag (n : nat) : mnat_auth := ◯ MaxNat n.

Section mnat_auth.
  Implicit Types (n : nat).

  Global Instance mnat_auth_frag_core_id n : CoreId (mnat_auth_frag n).
  Proof. apply _. Qed.

  Lemma mnat_auth_auth_frac_op q1 q2 n :
    mnat_auth_auth q1 n ⋅ mnat_auth_auth q2 n ≡ mnat_auth_auth (q1 + q2) n.
  Proof.
    rewrite /mnat_auth_auth auth_auth_frac_op.
    rewrite (comm _ (●{q2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mnat_auth_frag_op n1 n2 :
    mnat_auth_frag n1 ⋅ mnat_auth_frag n2 = mnat_auth_frag (n1 `max` n2).
  Proof. rewrite -auth_frag_op max_nat_op_max //. Qed.

  (** rephrasing of [mnat_auth_frag_op] useful for weakening a fragment to a
  smaller lower-bound *)
  Lemma mnat_auth_frag_op_le_l n n' :
    n' ≤ n →
    mnat_auth_frag n = mnat_auth_frag n' ⋅ mnat_auth_frag n.
  Proof. intros. rewrite mnat_auth_frag_op Nat.max_r //. Qed.

  Lemma mnat_auth_frac_op_valid q1 q2 n1 n2 :
    ✓ (mnat_auth_auth q1 n1 ⋅ mnat_auth_auth q2 n2) ↔ (q1 + q2 ≤ 1)%Qp ∧ n1 = n2.
  Proof.
    rewrite /mnat_auth_auth (comm _ (●{q2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_valid_op_l /auth_auth_frac_op_valid. naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_frac_op.
      by apply auth_both_frac_valid_discrete.
  Qed.

  Lemma mnat_auth_auth_op_valid n1 n2 :
    ✓ (mnat_auth_auth 1 n1 ⋅ mnat_auth_auth 1 n2) ↔ False.
  Proof. rewrite mnat_auth_frac_op_valid. naive_solver. Qed.

  Lemma mnat_auth_both_frac_valid q n m :
    ✓ (mnat_auth_auth q n ⋅ mnat_auth_frag m) ↔ (q ≤ 1)%Qp ∧ m ≤ n.
  Proof.
    rewrite /mnat_auth_auth /mnat_auth_frag -assoc -auth_frag_op.
    rewrite auth_both_frac_valid_discrete max_nat_included /=.
    naive_solver lia.
  Qed.

  Lemma mnat_auth_both_valid n m :
    ✓ (mnat_auth_auth 1 n ⋅ mnat_auth_frag m) ↔ m ≤ n.
  Proof. rewrite mnat_auth_both_frac_valid. naive_solver. Qed.

  Lemma mnat_auth_frag_mono n1 n2 : n1 ≤ n2 → mnat_auth_frag n1 ≼ mnat_auth_frag n2.
  Proof. intros. by apply auth_frag_mono, max_nat_included. Qed.

  Lemma mnat_auth_auth_valid n : ✓ mnat_auth_auth 1 n.
  Proof. by apply auth_both_valid. Qed.

  Lemma mnat_auth_included q n : mnat_auth_frag n ≼ mnat_auth_auth q n.
  Proof. apply cmra_included_r. Qed.

  Lemma mnat_auth_update n n' :
    n ≤ n' →
    mnat_auth_auth 1 n ~~> mnat_auth_auth 1 n'.
  Proof.
    intros. rewrite /mnat_auth_auth /mnat_auth_frag.
    by apply auth_update, max_nat_local_update.
  Qed.
End mnat_auth.

Typeclasses Opaque mnat_auth_auth mnat_auth_frag.
