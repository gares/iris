From iris.algebra Require Export auth.
From iris.algebra Require Import numbers updates.
From iris Require Import options.

(** Authoritative CMRA for [max_nat]. The authoritative element is a
monotonically increasing [nat], while a fragment is a lower bound. *)

Definition mnat_auth   := auth max_natUR.
Definition mnat_authR  := authR max_natUR.
Definition mnat_authUR := authUR max_natUR.

Section mnat_auth.
  Implicit Types (n : nat).

  Definition mnat_auth_auth (q : Qp) (n : nat) : mnat_auth := ●{q} MaxNat n.
  Definition mnat_auth_frag          (n : nat) : mnat_auth := ◯ MaxNat n.

  Global Instance mnat_auth_frag_core_id n : CoreId (mnat_auth_frag n).
  Proof. apply _. Qed.

  Lemma mnat_auth_auth_frac_op q1 q2 n :
    mnat_auth_auth q1 n ⋅ mnat_auth_auth q2 n ≡ mnat_auth_auth (q1 + q2) n.
  Proof. rewrite /mnat_auth_auth auth_auth_frac_op //. Qed.

  Lemma mnat_auth_auth_op_valid n1 n2 :
    ✓ (mnat_auth_auth 1 n1 ⋅ mnat_auth_auth 1 n2) ↔ False.
  Proof. rewrite auth_auth_op_valid //. Qed.

  Lemma mnat_auth_frac_op_valid q1 q2 n1 n2 :
    ✓ (mnat_auth_auth q1 n1 ⋅ mnat_auth_auth q2 n2) ↔ ✓ (q1 + q2)%Qp ∧ n1 = n2.
  Proof. rewrite auth_auth_frac_op_valid. naive_solver. Qed.

  Lemma mnat_auth_frag_op n1 n2 :
    mnat_auth_frag n1 ⋅ mnat_auth_frag n2 = mnat_auth_frag (n1 `max` n2).
  Proof. rewrite -auth_frag_op max_nat_op_max //. Qed.

  (** rephrasing of [mnat_auth_frag_op] useful for weakening a fragment to a
  smaller lower-bound *)
  Lemma mnat_auth_frag_op_le_l n n' :
    n' ≤ n →
    mnat_auth_frag n = mnat_auth_frag n' ⋅ mnat_auth_frag n.
  Proof.
    intros Hle.
    rewrite mnat_auth_frag_op.
    rewrite Nat.max_r //.
  Qed.

  Lemma mnat_auth_both_frac_valid q n m :
    ✓ (mnat_auth_auth q n ⋅ mnat_auth_frag m) ↔ ✓ q ∧ m ≤ n.
  Proof.
    rewrite auth_both_frac_valid_discrete.
    rewrite max_nat_included /=.
    naive_solver.
  Qed.

  Lemma mnat_auth_both_valid n m :
    ✓ (mnat_auth_auth 1 n ⋅ mnat_auth_frag m) ↔ m ≤ n.
  Proof. rewrite mnat_auth_both_frac_valid frac_valid'. naive_solver. Qed.

  Lemma mnat_auth_auth_valid n : ✓ mnat_auth_auth 1 n.
  Proof. apply auth_auth_valid; done. Qed.

  Lemma mnat_auth_update n n' :
    n ≤ n' →
    mnat_auth_auth 1 n ~~> mnat_auth_auth 1 n' ⋅ mnat_auth_frag n'.
  Proof.
    intros Hle.
    apply auth_update_alloc, max_nat_local_update; done.
  Qed.

  Lemma mnat_auth_alloc_frag q n :
    mnat_auth_auth q n ~~> mnat_auth_auth q n ⋅ mnat_auth_frag n.
  Proof. by apply (auth_update_frac_alloc _ _ _). Qed.
End mnat_auth.

Typeclasses Opaque mnat_auth_auth mnat_auth_frag.
