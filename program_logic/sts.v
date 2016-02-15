From algebra Require Export sts.
From algebra Require Import dra.
From program_logic Require Export invariants ghost_ownership.
Import uPred.

Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments unit _ _ !_ /.

Module sts.
(** This module is *not* meant to be imported. Instead, just use "sts.ctx" etc.
    like you would use "auth_ctx" etc. *)
Export algebra.sts.sts.

Record Sts {A B} := {
  st : relation A;
  tok    : A → set B;
}.
Arguments Sts : clear implicits.

Class InG Λ Σ (i : gid) {A B} (sts : Sts A B) := {
  inG :> ghost_ownership.InG Λ Σ i (stsRA sts.(st) sts.(tok));
  inh :> Inhabited A;
}.

Section definitions.
  Context {Λ Σ A B} (i : gid) (sts : Sts A B) `{!InG Λ Σ i sts} (γ : gname).
  Definition inv  (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ s, own i γ (sts_auth sts.(st) sts.(tok) s ∅) ★ φ s)%I.
  Definition states (S : set A) (T: set B) : iPropG Λ Σ :=
    (■ closed sts.(st) sts.(tok) S T ∧
     own i γ (sts_frag sts.(st) sts.(tok) S T))%I.
  Definition state (s : A) (T: set B) : iPropG Λ Σ :=
    own i γ (sts_frag sts.(st) sts.(tok) (sts.up sts.(st) sts.(tok) s T) T).
  Definition ctx (N : namespace) (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    invariants.inv N (inv φ).
End definitions.
Instance: Params (@inv) 8.
Instance: Params (@states) 8.
Instance: Params (@ctx) 9.

Section sts.
  Context {Λ Σ A B} (i : gid) (sts : Sts A B) `{!InG Λ Σ StsI sts}.
  Context (φ : A → iPropG Λ Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types γ : gname.

  Lemma alloc N s :
    φ s ⊑ pvs N N (∃ γ, ctx StsI sts γ N φ ∧ state StsI sts γ s (set_all ∖ sts.(tok) s)).
  Proof.
    eapply sep_elim_True_r.
    { eapply (own_alloc StsI (sts_auth sts.(st) sts.(tok) s (set_all ∖ sts.(tok) s)) N).
      apply discrete_valid=>/=. solve_elem_of. }
    rewrite pvs_frame_l. apply pvs_strip_pvs.
    rewrite sep_exist_l. apply exist_elim=>γ. rewrite -(exist_intro γ).
    transitivity (▷ inv StsI sts γ φ ★ state StsI sts γ s (set_all ∖ sts.(tok) s))%I.
    { rewrite /inv -later_intro -(exist_intro s).
      rewrite [(_ ★ φ _)%I]comm -assoc. apply sep_mono; first done.
      rewrite -own_op. apply equiv_spec, own_proper.
      split; first split; simpl.
      - intros; solve_elem_of-.
      - intros _. split_ands; first by solve_elem_of-.
        + apply closed_up. solve_elem_of-.
        + constructor; last solve_elem_of-. apply sts.elem_of_up. 
      - intros _. constructor. solve_elem_of-. }
    rewrite (inv_alloc N) /ctx pvs_frame_r. apply pvs_mono.
    by rewrite always_and_sep_l.
  Qed.

  Lemma opened E γ S T :
    (▷ inv StsI sts γ φ ★ own StsI γ (sts_frag sts.(st) sts.(tok) S T))
      ⊑ pvs E E (∃ s, ■ (s ∈ S) ★ ▷ φ s ★ own StsI γ (sts_auth sts.(st) sts.(tok) s T)).
  Proof.
    rewrite /inv. rewrite later_exist sep_exist_r. apply exist_elim=>s.
    rewrite later_sep pvs_timeless !pvs_frame_r. apply pvs_mono.
    rewrite -(exist_intro s).
    rewrite [(_ ★ ▷φ _)%I]comm -!assoc -own_op -[(▷φ _ ★ _)%I]comm.
    rewrite own_valid_l discrete_validI.
    rewrite -!assoc. apply const_elim_sep_l=>-[? [Hcl Hdisj]]. simpl in Hdisj, Hcl.
    inversion_clear Hdisj. rewrite const_equiv // left_id.
    rewrite comm. apply sep_mono; first done.
    apply equiv_spec, own_proper. split; first split; simpl.
    - intros Hdisj. split_ands; first by solve_elem_of-.
      + done.
      + constructor; [done | solve_elem_of-].
    - intros _. by eapply closed_disjoint.
    - intros _. constructor. solve_elem_of-.
  Qed.

  Lemma closing E γ s T s' S' T' :
    step sts.(st) sts.(tok) (s, T) (s', T') → s' ∈ S' → closed sts.(st) sts.(tok) S' T' →
    (▷ φ s' ★ own StsI γ (sts_auth sts.(st) sts.(tok) s T))
    ⊑ pvs E E (▷ inv StsI sts γ φ ★ own StsI γ (sts_frag sts.(st) sts.(tok) S' T')).
  Proof.
  Abort.

End sts.

End sts.
