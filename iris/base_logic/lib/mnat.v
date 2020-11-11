(** Ghost state for a monotonically increasing nat, wrapping the [mnat_authR]
RA. Provides an authoritative proposition [mnat_own_auth γ q n] for the
underlying number [n] and a persistent proposition [mnat_own_lb γ m] witnessing that
the authoritative nat is at least m.

The key rules are [mnat_own_lb_valid], which asserts that an auth at [n] and a
lower-bound at [m] imply that [m ≤ n], and [mnat_update], which allows to
increase the auth element. At any time the auth nat can be "snapshotted" with
[mnat_get_lb] to produce a persistent lower-bound proposition. *)

From iris.algebra.lib Require Import mnat_auth.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Class mnatG Σ :=
  MnatG { mnatG_inG :> inG Σ mnat_authR; }.
Definition mnatΣ : gFunctors := #[ GFunctor mnat_authR ].
Instance subG_mnatΣ Σ : subG mnatΣ Σ → mnatG Σ.
Proof. solve_inG. Qed.

Definition mnat_own_auth_def `{!mnatG Σ} (γ : gname) (q : Qp) (n : nat) : iProp Σ :=
  own γ (mnat_auth_auth q n).
Definition mnat_own_auth_aux : seal (@mnat_own_auth_def). Proof. by eexists. Qed.
Definition mnat_own_auth := mnat_own_auth_aux.(unseal).
Definition mnat_own_auth_eq : @mnat_own_auth = @mnat_own_auth_def := mnat_own_auth_aux.(seal_eq).
Arguments mnat_own_auth {Σ _} γ q n.

Definition mnat_own_lb_def `{!mnatG Σ} (γ : gname) (n : nat): iProp Σ :=
  own γ (mnat_auth_frag n).
Definition mnat_own_lb_aux : seal (@mnat_own_lb_def). Proof. by eexists. Qed.
Definition mnat_own_lb := mnat_own_lb_aux.(unseal).
Definition mnat_own_lb_eq : @mnat_own_lb = @mnat_own_lb_def := mnat_own_lb_aux.(seal_eq).
Arguments mnat_own_lb {Σ _} γ n.

Local Ltac unseal := rewrite
  ?mnat_own_auth_eq /mnat_own_auth_def
  ?mnat_own_lb_eq /mnat_own_lb_def.

Section mnat.
  Context `{!mnatG Σ}.
  Implicit Types (n m : nat).

  Global Instance mnat_own_auth_timeless γ q n : Timeless (mnat_own_auth γ q n).
  Proof. unseal. apply _. Qed.
  Global Instance mnat_own_lb_timeless γ n : Timeless (mnat_own_lb γ n).
  Proof. unseal. apply _. Qed.
  Global Instance mnat_own_lb_persistent γ n : Persistent (mnat_own_lb γ n).
  Proof. unseal. apply _. Qed.

  Global Instance mnat_own_auth_fractional γ n : Fractional (λ q, mnat_own_auth γ q n).
  Proof. unseal. intros p q. rewrite -own_op mnat_auth_auth_frac_op //. Qed.

  Global Instance mnat_own_auth_as_fractional γ q n :
    AsFractional (mnat_own_auth γ q n) (λ q, mnat_own_auth γ q n) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma mnat_own_auth_agree γ q1 q2 n1 n2 :
    mnat_own_auth γ q1 n1 -∗ mnat_own_auth γ q2 n2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ n1 = n2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%mnat_auth_frac_op_valid; done.
  Qed.

  Lemma mnat_own_auth_exclusive γ n1 n2 :
    mnat_own_auth γ 1 n1 -∗ mnat_own_auth γ 1 n2 -∗ False.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[]%mnat_auth_auth_op_valid.
  Qed.

  Lemma mnat_own_lb_valid γ q n m :
    mnat_own_auth γ q n -∗ mnat_own_lb γ m -∗ ⌜(q ≤ 1)%Qp ∧ m ≤ n⌝.
  Proof.
    unseal. iIntros "Hauth Hlb".
    iDestruct (own_valid_2 with "Hauth Hlb") as %Hvalid%mnat_auth_both_frac_valid.
    auto.
  Qed.

  (** The conclusion of this lemma is persistent; the proofmode will preserve the
  [mnat_own_auth] in the premise as long as the conclusion is introduced to the
  persistent context, for example with [iDestruct (mnat_get_lb with
  "Hauth") as "#Hfrag"]. *)
  Lemma mnat_get_lb γ q n :
    mnat_own_auth γ q n -∗ mnat_own_lb γ n.
  Proof. unseal. apply own_mono, mnat_auth_included. Qed.

  Lemma mnat_own_lb_le γ n n' :
    n' ≤ n →
    mnat_own_lb γ n -∗ mnat_own_lb γ n'.
  Proof. unseal. intros. by apply own_mono, mnat_auth_frag_mono. Qed.

  Lemma mnat_alloc n :
    ⊢ |==> ∃ γ, mnat_own_auth γ 1 n ∗ mnat_own_lb γ n.
  Proof.
    unseal.
    iMod (own_alloc (mnat_auth_auth 1 n ⋅ mnat_auth_frag n)) as (γ) "[??]".
    { apply mnat_auth_both_valid; auto. }
    auto with iFrame.
  Qed.

  Lemma mnat_update n' γ n :
    n ≤ n' →
    mnat_own_auth γ 1 n ==∗ mnat_own_auth γ 1 n'.
  Proof. unseal. intros. by apply own_update, mnat_auth_update. Qed.

  Lemma mnat_update_with_lb γ n n' :
    n ≤ n' →
    mnat_own_auth γ 1 n ==∗ mnat_own_auth γ 1 n' ∗ mnat_own_lb γ n'.
  Proof.
    iIntros (Hlb) "Hauth".
    iMod (mnat_update n' with "Hauth") as "Hauth"; auto.
    iDestruct (mnat_get_lb with "Hauth") as "#Hlb"; auto.
  Qed.
End mnat.
