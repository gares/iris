From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ownership ectx_lifting. (* for ownP *)
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import weakestpre.
Import uPred.
Local Hint Extern 0 (head_reducible _ _) => do_head_step eauto 2.

Section lifting.
Context `{irisG heap_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bind_ctxi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} ⊢
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateful reductions. *)
Lemma wp_alloc_pst E σ v Φ :
  ▷ ownP σ ★ ▷ (∀ l, σ !! l = None ∧ ownP (<[l:=v]>σ) ={E}=★ Φ (LitV (LitLoc l)))
  ⊢ WP Alloc (of_val v) @ E {{ Φ }}.
Proof.
  iIntros "[HP HΦ]".
  iApply (wp_lift_atomic_head_step (Alloc (of_val v)) σ); eauto.
  iFrame "HP". iNext. iIntros (v2 σ2 ef) "[% HP]". inv_head_step.
  match goal with H: _ = of_val v2 |- _ => apply (inj of_val (LitV _)) in H end.
  subst v2. iSplit; last done. iApply "HΦ"; by iSplit.
Qed.

Lemma wp_load_pst E σ l v Φ :
  σ !! l = Some v →
  ▷ ownP σ ★ ▷ (ownP σ ={E}=★ Φ v) ⊢ WP Load (Lit (LitLoc l)) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_head_step σ v σ []) ?right_id //;
    last (by intros; inv_head_step; eauto using to_of_val). solve_atomic.
Qed.

Lemma wp_store_pst E σ l v v' Φ :
  σ !! l = Some v' →
  ▷ ownP σ ★ ▷ (ownP (<[l:=v]>σ) ={E}=★ Φ (LitV LitUnit))
  ⊢ WP Store (Lit (LitLoc l)) (of_val v) @ E {{ Φ }}.
Proof.
  intros ?.
  rewrite-(wp_lift_atomic_det_head_step σ (LitV LitUnit) (<[l:=v]>σ) [])
    ?right_id //; last (by intros; inv_head_step; eauto). solve_atomic.
Qed.

Lemma wp_cas_fail_pst E σ l v1 v2 v' Φ :
  σ !! l = Some v' → v' ≠ v1 →
  ▷ ownP σ ★ ▷ (ownP σ ={E}=★ Φ (LitV $ LitBool false))
  ⊢ WP CAS (Lit (LitLoc l)) (of_val v1) (of_val v2) @ E {{ Φ }}.
Proof.
  intros ??.
  rewrite -(wp_lift_atomic_det_head_step σ (LitV $ LitBool false) σ [])
    ?right_id //; last (by intros; inv_head_step; eauto). solve_atomic.
Qed.

Lemma wp_cas_suc_pst E σ l v1 v2 Φ :
  σ !! l = Some v1 →
  ▷ ownP σ ★ ▷ (ownP (<[l:=v2]>σ) ={E}=★ Φ (LitV $ LitBool true))
  ⊢ WP CAS (Lit (LitLoc l)) (of_val v1) (of_val v2) @ E {{ Φ }}.
Proof.
  intros ?. rewrite -(wp_lift_atomic_det_head_step σ (LitV $ LitBool true)
    (<[l:=v2]>σ) []) ?right_id //; last (by intros; inv_head_step; eauto).
  solve_atomic.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e Φ :
  ▷ (|={E}=> Φ (LitV LitUnit)) ★ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) (Lit LitUnit) [e]) //=;
    last by intros; inv_head_step; eauto.
  by rewrite later_sep -(wp_value_pvs _ _ (Lit _)) // right_id.
Qed.

Lemma wp_rec E f x erec e1 e2 Φ :
  e1 = Rec f x erec →
  is_Some (to_val e2) →
  Closed (f :b: x :b: []) erec →
  ▷ WP subst' x e2 (subst' f e1 erec) @ E {{ Φ }} ⊢ WP App e1 e2 @ E {{ Φ }}.
Proof.
  intros -> [v2 ?] ?. rewrite -(wp_lift_pure_det_head_step (App _ _)
    (subst' x e2 (subst' f (Rec f x erec) erec)) []) //= ?right_id;
    intros; inv_head_step; eauto.
Qed.

Lemma wp_un_op E op l l' Φ :
  un_op_eval op l = Some l' →
  ▷ (|={E}=> Φ (LitV l')) ⊢ WP UnOp op (Lit l) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (UnOp op _) (Lit l') [])
    ?right_id -?wp_value_pvs //; intros; inv_head_step; eauto.
Qed.

Lemma wp_bin_op E op l1 l2 l' Φ :
  bin_op_eval op l1 l2 = Some l' →
  ▷ (|={E}=> Φ (LitV l')) ⊢ WP BinOp op (Lit l1) (Lit l2) @ E {{ Φ }}.
Proof.
  intros Heval. rewrite -(wp_lift_pure_det_head_step (BinOp op _ _) (Lit l') [])
    ?right_id -?wp_value_pvs //; intros; inv_head_step; eauto.
Qed.

Lemma wp_if_true E e1 e2 Φ :
  ▷ WP e1 @ E {{ Φ }} ⊢ WP If (Lit (LitBool true)) e1 e2 @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (If _ _ _) e1 [])
    ?right_id //; intros; inv_head_step; eauto.
Qed.

Lemma wp_if_false E e1 e2 Φ :
  ▷ WP e2 @ E {{ Φ }} ⊢ WP If (Lit (LitBool false)) e1 e2 @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (If _ _ _) e2 [])
    ?right_id //; intros; inv_head_step; eauto.
Qed.

Lemma wp_fst E e1 v1 e2 Φ :
  to_val e1 = Some v1 → is_Some (to_val e2) →
  ▷ (|={E}=> Φ v1) ⊢ WP Fst (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros ? [v2 ?]. rewrite -(wp_lift_pure_det_head_step (Fst _) e1 [])
    ?right_id -?wp_value_pvs //; intros; inv_head_step; eauto.
Qed.

Lemma wp_snd E e1 e2 v2 Φ :
  is_Some (to_val e1) → to_val e2 = Some v2 →
  ▷ (|={E}=> Φ v2) ⊢ WP Snd (Pair e1 e2) @ E {{ Φ }}.
Proof.
  intros [v1 ?] ?. rewrite -(wp_lift_pure_det_head_step (Snd _) e2 [])
    ?right_id -?wp_value_pvs //; intros; inv_head_step; eauto.
Qed.

Lemma wp_case_inl E e0 e1 e2 Φ :
  is_Some (to_val e0) →
  ▷ WP App e1 e0 @ E {{ Φ }} ⊢ WP Case (InjL e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros [v0 ?]. rewrite -(wp_lift_pure_det_head_step (Case _ _ _)
    (App e1 e0) []) ?right_id //; intros; inv_head_step; eauto.
Qed.

Lemma wp_case_inr E e0 e1 e2 Φ :
  is_Some (to_val e0) →
  ▷ WP App e2 e0 @ E {{ Φ }} ⊢ WP Case (InjR e0) e1 e2 @ E {{ Φ }}.
Proof.
  intros [v0 ?]. rewrite -(wp_lift_pure_det_head_step (Case _ _ _)
    (App e2 e0) []) ?right_id //; intros; inv_head_step; eauto.
Qed.
End lifting.
