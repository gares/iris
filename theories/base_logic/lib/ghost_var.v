(** A simple "ghost variable" of arbitrary type with fractional ownership.
Can be mutated when fully owned. *)
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_agree.
From iris.base_logic.lib Require Export own.
From iris Require Import options.

(** The CMRA we need. *)
Class ghost_varG Σ (A : Type) := GhostVarG {
  ghost_var_inG :> inG Σ (frac_agreeR $ leibnizO A);
}.
Definition ghost_varΣ (A : Type) : gFunctors := #[ GFunctor (frac_agreeR $ leibnizO A) ].

Instance subG_ghost_varΣ Σ A : subG (ghost_varΣ A) Σ → ghost_varG Σ A.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!ghost_varG Σ A} (γ : gname).

  Definition ghost_var (q : Qp) (a : A) : iProp Σ :=
    own γ (to_frac_agree (A:=leibnizO A) q a).
End definitions.

Section lemmas.
  Context `{!ghost_varG Σ A}.
  Implicit Types (a : A) (q : Qp).

  Global Instance ghost_var_timeless γ q a : Timeless (ghost_var γ q a).
  Proof. apply _. Qed.

  Global Instance ghost_var_fractional γ a : Fractional (λ q, ghost_var γ q a).
  Proof. intros q1 q2. rewrite /ghost_var -own_op -pair_op agree_idemp //. Qed.
  Global Instance ghost_var_as_fractional γ a q :
    AsFractional (ghost_var γ q a) (λ q, ghost_var γ q a) q.
  Proof. split. done. apply _. Qed.

  Lemma ghost_var_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_var γ 1 a.
  Proof. intros. iApply own_alloc_strong; done. Qed.
  Lemma ghost_var_alloc a :
    ⊢ |==> ∃ γ, ghost_var γ 1 a.
  Proof. iApply own_alloc. done. Qed.

  Lemma ghost_var_op_valid γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜✓ (q1 + q2)%Qp ∧ a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (own_valid_2 with "Hvar1 Hvar2") as %[Hq Ha]%frac_agree_op_valid.
    done.
  Qed.

  (** This is just an instance of fractionality above, but that can be hard to find. *)
  Lemma ghost_var_split γ a q1 q2 :
    ghost_var γ (q1 + q2) a -∗ ghost_var γ q1 a ∗ ghost_var γ q2 a.
  Proof. iIntros "[$$]". Qed.

  (** Update the ghost variable to new value [b]. *)
  Lemma ghost_var_update b γ a :
    ghost_var γ 1 a ==∗ ghost_var γ 1 b.
  Proof.
    iApply own_update. apply cmra_update_exclusive. done.
  Qed. 

End lemmas.

Typeclasses Opaque ghost_var.
