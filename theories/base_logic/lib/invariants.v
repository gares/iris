From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap.
From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Import wsat.
Set Default Proof Using "Type".
Import uPred.


Lemma fresh_inv_name (E : gset positive) N : ∃ i, i ∉ E ∧ i ∈ (↑N:coPset).
Proof.
  exists (coPpick (↑ N ∖ gset_to_coPset E)).
  rewrite -elem_of_gset_to_coPset (comm and) -elem_of_difference.
  apply coPpick_elem_of=> Hfin.
  eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
  apply gset_to_coPset_finite.
Qed.

(** * Invariants *)
Section inv.
  Context `{!invG Σ}.

  (** Internal backing store of invariants *)
  Definition internal_inv_def (N : namespace) (P : iProp Σ) : iProp Σ :=
    (∃ i P', ⌜i ∈ (↑N:coPset)⌝ ∧ ▷ □ (P' ↔ P) ∧ ownI i P')%I.
  Definition internal_inv_aux : seal (@internal_inv_def). by eexists. Qed.
  Definition internal_inv := internal_inv_aux.(unseal).
  Definition internal_inv_eq : @internal_inv = @internal_inv_def := internal_inv_aux.(seal_eq).
  Typeclasses Opaque internal_inv.

  Global Instance internal_inv_persistent N P : Persistent (internal_inv N P).
  Proof. rewrite internal_inv_eq /internal_inv; apply _. Qed.

  Lemma internal_inv_open E N P :
  ↑N ⊆ E → internal_inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    rewrite internal_inv_eq /internal_inv_def uPred_fupd_eq /uPred_fupd_def.
    iDestruct 1 as (i P') "(Hi & #HP' & #HiP)".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
    rewrite {1 4}(union_difference_L (↑ N) E) // ownE_op; last set_solver.
    rewrite {1 5}(union_difference_L {[ i ]} (↑ N)) // ownE_op; last set_solver.
    iIntros "(Hw & [HE $] & $) !> !>".
    iDestruct (ownI_open i with "[$Hw $HE $HiP]") as "($ & HP & HD)".
    iDestruct ("HP'" with "HP") as "$".
    iIntros "HP [Hw $] !> !>". iApply (ownI_close _ P'). iFrame "HD Hw HiP".
    iApply "HP'". iFrame.
  Qed.

  Lemma internal_inv_alloc N E P : ▷ P ={E}=∗ internal_inv N P.
  Proof.
    rewrite internal_inv_eq /internal_inv_def uPred_fupd_eq. iIntros "HP [Hw $]".
    iMod (ownI_alloc (.∈ (↑N : coPset)) P with "[$HP $Hw]")
      as (i ?) "[$ ?]"; auto using fresh_inv_name.
    do 2 iModIntro. iExists i, P. rewrite -(iff_refl True%I). auto.
  Qed.

  Lemma internal_inv_alloc_open N E P :
    ↑N ⊆ E → (|={E, E∖↑N}=> internal_inv N P ∗ (▷P ={E∖↑N, E}=∗ True))%I.
  Proof.
    rewrite internal_inv_eq /internal_inv_def uPred_fupd_eq. iIntros (Sub) "[Hw HE]".
    iMod (ownI_alloc_open (.∈ (↑N : coPset)) P with "Hw")
      as (i ?) "(Hw & #Hi & HD)"; auto using fresh_inv_name.
    iAssert (ownE {[i]} ∗ ownE (↑ N ∖ {[i]}) ∗ ownE (E ∖ ↑ N))%I
      with "[HE]" as "(HEi & HEN\i & HE\N)".
    { rewrite -?ownE_op; [|set_solver..].
      rewrite assoc_L -!union_difference_L //. set_solver. }
    do 2 iModIntro. iFrame "HE\N". iSplitL "Hw HEi"; first by iApply "Hw".
    iSplitL "Hi".
    { iExists i, P. rewrite -(iff_refl True%I). auto. }
    iIntros "HP [Hw HE\N]".
    iDestruct (ownI_close with "[$Hw $Hi $HP $HD]") as "[$ HEi]".
    do 2 iModIntro. iSplitL; [|done].
    iCombine "HEi HEN\i HE\N" as "HEN".
    rewrite -?ownE_op; [|set_solver..].
    rewrite assoc_L -!union_difference_L //; set_solver.
  Qed.

  (** Invariants API *)
  Definition inv_def (N: namespace) (P: iProp Σ) : iProp Σ :=
    (□ (∀ E, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ True)))%I.
  Definition inv_aux : seal (@inv_def). by eexists. Qed.
  Definition inv := inv_aux.(unseal).
  Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).
  Typeclasses Opaque inv.

  (** Properties about invariants *)
  Global Instance inv_contractive N: Contractive (inv N).
  Proof. rewrite inv_eq. solve_contractive. Qed.

  Global Instance inv_ne N : NonExpansive (inv N).
  Proof. apply contractive_ne, _. Qed.

  Global Instance inv_proper N: Proper (equiv ==> equiv) (inv N).
  Proof. apply ne_proper, _. Qed.

  Global Instance inv_persistent M P: Persistent (inv M P).
  Proof. rewrite inv_eq. typeclasses eauto. Qed.

  Lemma inv_acc N P Q:
    inv N P -∗ ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q.
  Proof.
    iIntros "#I #Acc". rewrite inv_eq.
    iModIntro. iIntros (E H). iDestruct ("I" $! E H) as "#I'".
    iApply fupd_wand_r. iFrame "I'".
    iIntros "(P & Hclose)". iSpecialize ("Acc" with "P").
    iDestruct "Acc" as "[Q CB]". iFrame.
    iIntros "Q". iApply "Hclose". now iApply "CB".
  Qed.

  Lemma inv_iff N P Q : ▷ □ (P ↔ Q) -∗ inv N P -∗ inv N Q.
  Proof.
    iIntros "#HPQ #I". iApply (inv_acc with "I").
    iNext. iIntros "!# P". iSplitL "P".
    - by iApply "HPQ".
    - iIntros "Q". by iApply "HPQ".
  Qed.

  Lemma inv_to_inv M P: internal_inv M P  -∗ inv M P.
  Proof.
    iIntros "#I". rewrite inv_eq. iIntros (E H).
    iPoseProof (internal_inv_open with "I") as "H"; eauto.
  Qed.

  Lemma inv_alloc N E P : ▷ P ={E}=∗ inv N P.
  Proof.
    iIntros "P". iPoseProof (internal_inv_alloc  N E with "P") as "I".
    iApply fupd_mono; last eauto.
    iApply inv_to_inv.
  Qed.

  Lemma inv_alloc_open N E P :
    ↑N ⊆ E → (|={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ True))%I.
  Proof.
    iIntros (H). iPoseProof (internal_inv_alloc_open _ _ _ H) as "H".
    iApply fupd_mono; last eauto.
    iIntros "[I H]"; iFrame; by iApply inv_to_inv.
  Qed.

  Lemma inv_open E N P :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    rewrite inv_eq /inv_def; iIntros (H) "#I". by iApply "I".
  Qed.

  Lemma inv_open_strong E N P :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ True.
  Proof.
      iIntros (?) "Hinv".      iPoseProof (inv_open (↑ N) N P with "Hinv") as "H"; first done.
      rewrite difference_diag_L.
      iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
      rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
      iIntros (E') "HP".
      iPoseProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
        by rewrite left_id_L.
  Qed.

  Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

  Global Instance into_acc_inv N P E:
    IntoAcc (X := unit) (inv N P)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite inv_eq /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". iApply "Hinv"; done.
  Qed.

  Lemma inv_open_timeless E N P `{!Timeless P} :
    ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "Hinv". iMod (inv_open with "Hinv") as "[>HP Hclose]"; auto.
    iIntros "!> {$HP} HP". iApply "Hclose"; auto.
  Qed.

  (* Weakening of semantic invariants *)
  Lemma inv_proj_l N P Q: inv N (P ∗ Q) -∗ inv N P.
  Proof.
    iIntros "#I". iApply inv_acc; eauto.
    iNext. iIntros "!# [$ Q] P"; iFrame.
  Qed.

  Lemma inv_proj_r N P Q: inv N (P ∗ Q) -∗ inv N Q.
  Proof.
    rewrite (bi.sep_comm P Q). eapply inv_proj_l.
  Qed.

  Lemma inv_split N P Q: inv N (P ∗ Q) -∗ inv N P ∗ inv N Q.
  Proof.
    iIntros "#H".
    iPoseProof (inv_proj_l with "H") as "$".
    iPoseProof (inv_proj_r with "H") as "$".
  Qed.

End inv.
