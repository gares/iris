From iris.bi Require Export bi.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".

(** This proves that we need the ▷ in a "Saved Proposition" construction with
name-dependent allocation. *)
Module savedprop. Section savedprop.
  Context `{BiAffine PROP}.
  Notation "¬ P" := (□ (P → False))%I : bi_scope.
  Implicit Types P : PROP.

  Context (bupd : PROP → PROP).
  Notation "|==> Q" := (bupd Q)
    (at level 99, Q at level 200, format "|==>  Q") : bi_scope.

  Hypothesis bupd_intro : ∀ P, P ⊢ |==> P.
  Hypothesis bupd_mono : ∀ P Q, (P ⊢ Q) → (|==> P) ⊢ |==> Q.
  Hypothesis bupd_trans : ∀ P, (|==> |==> P) ⊢ |==> P.
  Hypothesis bupd_frame_r : ∀ P R, (|==> P) ∗ R ⊢ |==> (P ∗ R).

  Context (ident : Type) (saved : ident → PROP → PROP).
  Hypothesis sprop_persistent : ∀ i P, Persistent (saved i P).
  Hypothesis sprop_alloc_dep :
    ∀ (P : ident → PROP), (|==> ∃ i, saved i (P i))%I.
  Hypothesis sprop_agree : ∀ i P Q, saved i P ∧ saved i Q ⊢ □ (P ↔ Q).

  (** We assume that we cannot update to false. *)
  Hypothesis consistency : ¬(|==> False)%I.

  Instance bupd_mono' : Proper ((⊢) ==> (⊢)) bupd.
  Proof. intros P Q ?. by apply bupd_mono. Qed.
  Instance elim_modal_bupd p P Q : ElimModal True p false (|==> P) P (|==> Q) (|==> Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      bupd_frame_r bi.wand_elim_r bupd_trans.
  Qed.

  (** A bad recursive reference: "Assertion with name [i] does not hold" *)
  Definition A (i : ident) : PROP := (∃ P, ¬ P ∗ saved i P)%I.

  Lemma A_alloc : (|==> ∃ i, saved i (A i))%I.
  Proof. by apply sprop_alloc_dep. Qed.

  Lemma saved_NA i : saved i (A i) ⊢ ¬ A i.
  Proof.
    iIntros "#Hs !# #HA". iPoseProof "HA" as "HA'".
    iDestruct "HA'" as (P) "[#HNP HsP]". iApply "HNP".
    iDestruct (sprop_agree i P (A i) with "[]") as "#[_ HP]".
    { eauto. }
    iApply "HP". done.
  Qed.

  Lemma saved_A i : saved i (A i) ⊢ A i.
  Proof.
    iIntros "#Hs". iExists (A i). iFrame "#".
    by iApply saved_NA.
  Qed.

  Lemma contradiction : False.
  Proof using All.
    apply consistency.
    iMod A_alloc as (i) "#H".
    iPoseProof (saved_NA with "H") as "HN".
    iApply bupd_intro. iApply "HN". iApply saved_A. done.
  Qed.
End savedprop. End savedprop.


(** This proves that we need the ▷ when opening invariants. *)
Module inv. Section inv.
  Context `{BiAffine PROP}.
  Implicit Types P : PROP.

  (** Assumptions *)
  (** We have the update modality (two classes: empty/full mask) *)
  Inductive mask := M0 | M1.
  Context (fupd : mask → PROP → PROP).
  Arguments fupd _ _%I.
  Hypothesis fupd_intro : ∀ E P, P ⊢ fupd E P.
  Hypothesis fupd_mono : ∀ E P Q, (P ⊢ Q) → fupd E P ⊢ fupd E Q.
  Hypothesis fupd_fupd : ∀ E P, fupd E (fupd E P) ⊢ fupd E P.
  Hypothesis fupd_frame_l : ∀ E P Q, P ∗ fupd E Q ⊢ fupd E (P ∗ Q).
  Hypothesis fupd_mask_mono : ∀ P, fupd M0 P ⊢ fupd M1 P.

  (** We have invariants *)
  Context (name : Type) (inv : name → PROP → PROP).
  Arguments inv _ _%I.
  Hypothesis inv_persistent : ∀ i P, Persistent (inv i P).
  Hypothesis inv_alloc : ∀ P, P ⊢ fupd M1 (∃ i, inv i P).
  Hypothesis inv_open :
    ∀ i P Q R, (P ∗ Q ⊢ fupd M0 (P ∗ R)) → (inv i P ∗ Q ⊢ fupd M1 R).

  (* We have tokens for a little "two-state STS": [start] -> [finish].
     state. [start] also asserts the exact state; it is only ever owned by the
     invariant.  [finished] is duplicable. *)
  (* Posssible implementations of these axioms:
     * Using the STS monoid of a two-state STS, where [start] is the
       authoritative saying the state is exactly [start], and [finish]
       is the "we are at least in state [finish]" typically owned by threads.
     * Ex () +_## ()
  *)
  Context (gname : Type).
  Context (start finished : gname → PROP).

  Hypothesis sts_alloc : fupd M0 (∃ γ, start γ).
  Hypotheses start_finish : ∀ γ, start γ ⊢ fupd M0 (finished γ).

  Hypothesis finished_not_start : ∀ γ, start γ ∗ finished γ ⊢ False.

  Hypothesis finished_dup : ∀ γ, finished γ ⊢ finished γ ∗ finished γ.

  (** We assume that we cannot update to false. *)
  Hypothesis consistency : ¬ (fupd M1 False).

  (** Some general lemmas and proof mode compatibility. *)
  Lemma inv_open' i P R : inv i P ∗ (P -∗ fupd M0 (P ∗ fupd M1 R)) ⊢ fupd M1 R.
  Proof.
    iIntros "(#HiP & HP)". iApply fupd_fupd. iApply inv_open; last first.
    { iSplit; first done. iExact "HP". }
    iIntros "(HP & HPw)". by iApply "HPw".
  Qed.

  Instance fupd_mono' E : Proper ((⊢) ==> (⊢)) (fupd E).
  Proof. intros P Q ?. by apply fupd_mono. Qed.
  Instance fupd_proper E : Proper ((⊣⊢) ==> (⊣⊢)) (fupd E).
  Proof.
    intros P Q; rewrite !bi.equiv_spec=> -[??]; split; by apply fupd_mono.
  Qed.

  Lemma fupd_frame_r E P Q : fupd E P ∗ Q ⊢ fupd E (P ∗ Q).
  Proof. by rewrite comm fupd_frame_l comm. Qed.

  Global Instance elim_fupd_fupd p E P Q :
    ElimModal True p false (fupd E P) P (fupd E Q) (fupd E Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_fupd.
  Qed.

  Global Instance elim_fupd0_fupd1 p P Q :
    ElimModal True p false (fupd M0 P) P (fupd M1 Q) (fupd M1 Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_mask_mono fupd_fupd.
  Qed.

  Global Instance exists_split_fupd0 {A} E P (Φ : A → PROP) :
    FromExist P Φ → FromExist (fupd E P) (λ a, fupd E (Φ a)).
  Proof.
    rewrite /FromExist=>HP. apply bi.exist_elim=> a.
    apply fupd_mono. by rewrite -HP -(bi.exist_intro a).
  Qed.

  (** Now to the actual counterexample. We start with a weird form of saved propositions. *)
  Definition saved (γ : gname) (P : PROP) : PROP :=
    (∃ i, inv i (start γ ∨ (finished γ ∗ □ P)))%I.
  Global Instance saved_persistent γ P : Persistent (saved γ P) := _.

  Lemma saved_alloc (P : gname → PROP) : fupd M1 (∃ γ, saved γ (P γ)).
  Proof.
    iIntros "". iMod (sts_alloc) as (γ) "Hs".
    iMod (inv_alloc (start γ ∨ (finished γ ∗ □ (P γ)))%I with "[Hs]") as (i) "#Hi".
    { auto. }
    iApply fupd_intro. by iExists γ, i.
  Qed.

  Lemma saved_cast γ P Q : saved γ P ∗ saved γ Q ∗ □ P ⊢ fupd M1 (□ Q).
  Proof.
    iIntros "(#HsP & #HsQ & #HP)". iDestruct "HsP" as (i) "HiP".
    iApply (inv_open' i). iSplit; first done.
    iIntros "HaP". iAssert (fupd M0 (finished γ)) with "[HaP]" as "> Hf".
    { iDestruct "HaP" as "[Hs | [Hf _]]".
      - by iApply start_finish.
      - by iApply fupd_intro. }
    iDestruct (finished_dup with "Hf") as "[Hf Hf']".
    iApply fupd_intro. iSplitL "Hf'"; first by eauto.
    (* Step 2: Open the Q-invariant. *)
    iClear (i) "HiP ". iDestruct "HsQ" as (i) "HiQ".
    iApply (inv_open' i). iSplit; first done.
    iIntros "[HaQ | [_ #HQ]]".
    { iExFalso. iApply finished_not_start. by iFrame. }
    iApply fupd_intro. iSplitL "Hf".
    { iRight. by iFrame. }
    by iApply fupd_intro.
  Qed.

  (** And now we tie a bad knot. *)
  Notation "¬ P" := (□ (P -∗ fupd M1 False))%I : bi_scope.
  Definition A i : PROP := (∃ P, ¬P ∗ saved i P)%I.
  Global Instance A_persistent i : Persistent (A i) := _.

  Lemma A_alloc : fupd M1 (∃ i, saved i (A i)).
  Proof. by apply saved_alloc. Qed.

  Lemma saved_NA i : saved i (A i) ⊢ ¬A i.
  Proof.
    iIntros "#Hi !# #HA". iPoseProof "HA" as "HA'".
    iDestruct "HA'" as (P) "#[HNP Hi']".
    iMod (saved_cast i (A i) P with "[]") as "HP".
    { eauto. }
    by iApply "HNP".
  Qed.

  Lemma saved_A i : saved i (A i) ⊢ A i.
  Proof.
    iIntros "#Hi". iExists (A i). iFrame "#".
    by iApply saved_NA.
  Qed.

  Lemma contradiction : False.
  Proof using All.
    apply consistency. iIntros "".
    iMod A_alloc as (i) "#H".
    iPoseProof (saved_NA with "H") as "HN".
    iApply "HN". iApply saved_A. done.
  Qed.
End inv. End inv.

(** This proves that if we have linear impredicative invariants, we can still
drop arbitrary resources (i.e., we can "defeat" linearity).
Variant 1: a strong invariant creation lemma that lets us create invariants
in the "open" state. *)
Module linear1. Section linear1.
  Context {PROP: sbi}.
  Implicit Types P : PROP.

  (** Assumptions. *)
  (** We have the mask-changing update modality (two classes: empty/full mask) *)
  Inductive mask := M0 | M1.
  Context (fupd : mask → mask → PROP → PROP).
  Arguments fupd _ _ _%I.
  Hypothesis fupd_intro : ∀ E P, P ⊢ fupd E E P.
  Hypothesis fupd_mono : ∀ E1 E2 P Q, (P ⊢ Q) → fupd E1 E2 P ⊢ fupd E1 E2 Q.
  Hypothesis fupd_fupd : ∀ E1 E2 E3 P, fupd E1 E2 (fupd E2 E3 P) ⊢ fupd E1 E3 P.
  Hypothesis fupd_frame_l : ∀ E1 E2 P Q, P ∗ fupd E1 E2 Q ⊢ fupd E1 E2 (P ∗ Q).

  (** We have cancelable invariants. (Really they would have fractions at
  [cinv_own] but we do not need that. They would also have a name matching
  the [mask] type, but we do not need that either.) *)
  Context (gname : Type) (cinv : gname → PROP → PROP) (cinv_own : gname → PROP).
  Hypothesis cinv_alloc_open :  ∀ P,
    (fupd M1 M0 (∃ γ, cinv γ P ∗ cinv_own γ ∗ (▷ P -∗ fupd M0 M1 emp)))%I.

  (** Some general lemmas and proof mode compatibility. *)
  Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (fupd E1 E2).
  Proof. intros P Q ?. by apply fupd_mono. Qed.
  Instance fupd_proper E1 E2 : Proper ((⊣⊢) ==> (⊣⊢)) (fupd E1 E2).
  Proof.
    intros P Q; rewrite !bi.equiv_spec=> -[??]; split; by apply fupd_mono.
  Qed.

  Lemma fupd_frame_r E1 E2 P Q : fupd E1 E2 P ∗ Q ⊢ fupd E1 E2 (P ∗ Q).
  Proof. by rewrite comm fupd_frame_l comm. Qed.

  Global Instance elim_fupd_fupd p E1 E2 E3 P Q :
    ElimModal True p false (fupd E1 E2 P) P (fupd E1 E3 Q) (fupd E2 E3 Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_fupd.
  Qed.

  (** Counterexample: now we can make any resource disappear. *)
  Lemma leak P : P -∗ fupd M1 M1 emp.
  Proof.
    iIntros "HP".
    set (INV := (∃ γ Q, cinv γ Q ∗ cinv_own γ ∗ P)%I).
    iMod (cinv_alloc_open INV) as (γ) "(Hinv & Htok & Hclose)".
    iApply "Hclose". iNext. iExists γ, _. iFrame.
  Qed.
End linear1. End linear1.

(** This proves that if we have linear impredicative invariants, we can still
drop arbitrary resources (i.e., we can "defeat" linearity).
Variant 2: the invariant can depend on the chose gname, and we also have
an accessor that gives back the invariant token immediately,
not just after the invariant got closed again. *)
Module linear2. Section linear2.
  Context {PROP: sbi}.
  Implicit Types P : PROP.

  (** Assumptions. *)
  (** We have the mask-changing update modality (two classes: empty/full mask) *)
  Inductive mask := M0 | M1.
  Context (fupd : mask → mask → PROP → PROP).
  Arguments fupd _ _ _%I.
  Hypothesis fupd_intro : ∀ E P, P ⊢ fupd E E P.
  Hypothesis fupd_mono : ∀ E1 E2 P Q, (P ⊢ Q) → fupd E1 E2 P ⊢ fupd E1 E2 Q.
  Hypothesis fupd_fupd : ∀ E1 E2 E3 P, fupd E1 E2 (fupd E2 E3 P) ⊢ fupd E1 E3 P.
  Hypothesis fupd_frame_l : ∀ E1 E2 P Q, P ∗ fupd E1 E2 Q ⊢ fupd E1 E2 (P ∗ Q).

  (** We have cancelable invariants. (Really they would have fractions at
  [cinv_own] but we do not need that. They would also have a name matching
  the [mask] type, but we do not need that either.) *)
  Context (gname : Type) (cinv : gname → PROP → PROP) (cinv_own : gname → PROP).
  Hypothesis cinv_alloc : ∀ E,
    fupd E E (∃ γ, cinv_own γ ∗ (∀ P, ▷ P -∗ fupd E E (cinv γ P)))%I.
  Hypothesis cinv_access : ∀ P γ,
    cinv γ P -∗ cinv_own γ -∗ fupd M1 M0 (▷ P ∗ cinv_own γ ∗ (▷ P -∗ fupd M0 M1 emp)).
  Hypothesis cinv_own_excl : ∀ E γ,
    ▷ cinv_own γ -∗ ▷ cinv_own γ -∗ fupd E E False.

  (** Some general lemmas and proof mode compatibility. *)
  Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (fupd E1 E2).
  Proof. intros P Q ?. by apply fupd_mono. Qed.
  Instance fupd_proper E1 E2 : Proper ((⊣⊢) ==> (⊣⊢)) (fupd E1 E2).
  Proof.
    intros P Q; rewrite !bi.equiv_spec=> -[??]; split; by apply fupd_mono.
  Qed.

  Lemma fupd_frame_r E1 E2 P Q : fupd E1 E2 P ∗ Q ⊢ fupd E1 E2 (P ∗ Q).
  Proof. by rewrite comm fupd_frame_l comm. Qed.

  Global Instance elim_fupd_fupd p E1 E2 E3 P Q :
    ElimModal True p false (fupd E1 E2 P) P (fupd E1 E3 Q) (fupd E2 E3 Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_fupd.
  Qed.

  (** Counterexample: now we can make any resource disappear. *)
  Lemma leak P : P -∗ fupd M1 M1 emp.
  Proof.
    iIntros "HP".
    iMod cinv_alloc as (γ) "(Htok & Hmkinv)".
    set (INV := (P ∨ cinv_own γ ∗ P)%I).
    iMod ("Hmkinv" $! INV with "[HP]") as "Hinv".
    { iLeft. done. }
    iMod (cinv_access with "Hinv Htok") as "([HP|Hinv] & Htok & Hclose)"; last first.
    { iDestruct "Hinv" as "(Htok' & ?)".
      iMod (cinv_own_excl with "Htok Htok'") as "[]". }
    iApply "Hclose". iNext. iRight. iFrame.
  Qed.
End linear2. End linear2.
