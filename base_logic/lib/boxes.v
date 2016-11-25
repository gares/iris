From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import auth gmap agree.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
Import uPred.

(** The CMRAs we need. *)
Class boxG Σ :=
  boxG_inG :> inG Σ (prodR
    (authR (optionUR (exclR boolC)))
    (optionR (agreeR (laterC (iPreProp Σ))))).

Section box_defs.
  Context `{invG Σ, boxG Σ} (N : namespace).

  Definition slice_name := gname.

  Definition box_own_auth (γ : slice_name) (a : auth (option (excl bool)))
    := own γ (a, (∅:option (agree (later (iPreProp Σ))))).

  Definition box_own_prop (γ : slice_name) (P : iProp Σ) : iProp Σ :=
    own γ (∅:auth (option (excl bool)), Some (to_agree (Next (iProp_unfold P)))).

  Definition slice_inv (γ : slice_name) (P : iProp Σ) : iProp Σ :=
    (∃ b, box_own_auth γ (● Excl' b) ∗ if b then P else True)%I.

  Definition slice (γ : slice_name) (P : iProp Σ) : iProp Σ :=
    (box_own_prop γ P ∗ inv N (slice_inv γ P))%I.

  Definition box (f : gmap slice_name bool) (P : iProp Σ) : iProp Σ :=
    (∃ Φ : slice_name → iProp Σ,
      ▷ (P ≡ [∗ map] γ ↦ b ∈ f, Φ γ) ∗
      [∗ map] γ ↦ b ∈ f, box_own_auth γ (◯ Excl' b) ∗ box_own_prop γ (Φ γ) ∗
                         inv N (slice_inv γ (Φ γ)))%I.
End box_defs.

Instance: Params (@box_own_prop) 3.
Instance: Params (@slice_inv) 3.
Instance: Params (@slice) 5.
Instance: Params (@box) 5.

Section box.
Context `{invG Σ, boxG Σ} (N : namespace).
Implicit Types P Q : iProp Σ.

Global Instance box_own_prop_ne n γ : Proper (dist n ==> dist n) (box_own_prop γ).
Proof. solve_proper. Qed.
Global Instance box_inv_ne n γ : Proper (dist n ==> dist n) (slice_inv γ).
Proof. solve_proper. Qed.
Global Instance slice_ne n γ : Proper (dist n ==> dist n) (slice N γ).
Proof. solve_proper. Qed.
Global Instance box_contractive f : Contractive (box N f).
Proof.
  intros n P1 P2 HP1P2. apply exist_ne. intros Φ. f_equiv; last done.
  apply contractive. intros n' ?. by rewrite HP1P2.
Qed.

Global Instance slice_persistent γ P : PersistentP (slice N γ P).
Proof. apply _. Qed.

Lemma box_own_auth_agree γ b1 b2 :
  box_own_auth γ (● Excl' b1) ∗ box_own_auth γ (◯ Excl' b2) ⊢ ⌜b1 = b2⌝.
Proof.
  rewrite /box_own_prop -own_op own_valid prod_validI /= and_elim_l.
  by iDestruct 1 as % [[[] [=]%leibniz_equiv] ?]%auth_valid_discrete.
Qed.

Lemma box_own_auth_update γ b1 b2 b3 :
  box_own_auth γ (● Excl' b1) ∗ box_own_auth γ (◯ Excl' b2)
  ==∗ box_own_auth γ (● Excl' b3) ∗ box_own_auth γ (◯ Excl' b3).
Proof.
  rewrite /box_own_auth -!own_op. apply own_update, prod_update; last done.
  by apply auth_update, option_local_update, exclusive_local_update.
Qed.

Lemma box_own_agree γ Q1 Q2 :
  box_own_prop γ Q1 ∗ box_own_prop γ Q2 ⊢ ▷ (Q1 ≡ Q2).
Proof.
  rewrite /box_own_prop -own_op own_valid prod_validI /= and_elim_r.
  rewrite option_validI /= agree_validI agree_equivI later_equivI /=.
  iIntros "#HQ". iNext. rewrite -{2}(iProp_fold_unfold Q1).
  iRewrite "HQ". by rewrite iProp_fold_unfold.
Qed.

Lemma box_alloc : box N ∅ True%I.
Proof.
  iIntros; iExists (λ _, True)%I; iSplit.
  - iNext. by rewrite big_sepM_empty.
  - by rewrite big_sepM_empty.
Qed.

Lemma box_insert_empty Q E f P :
  ▷ box N f P ={E}=∗ ∃ γ, ⌜f !! γ = None⌝ ∗
    slice N γ Q ∗ ▷ box N (<[γ:=false]> f) (Q ∗ P).
Proof.
  iDestruct 1 as (Φ) "[#HeqP Hf]".
  iMod (own_alloc_strong (● Excl' false ⋅ ◯ Excl' false,
    Some (to_agree (Next (iProp_unfold Q)))) (dom _ f))
    as (γ) "[Hdom Hγ]"; first done.
  rewrite pair_split. iDestruct "Hγ" as "[[Hγ Hγ'] #HγQ]".
  iDestruct "Hdom" as % ?%not_elem_of_dom.
  iMod (inv_alloc N _ (slice_inv γ Q) with "[Hγ]") as "#Hinv".
  { iNext. iExists false; eauto. }
  iModIntro; iExists γ; repeat iSplit; auto.
  iNext. iExists (<[γ:=Q]> Φ); iSplit.
  - iNext. iRewrite "HeqP". by rewrite big_sepM_fn_insert'.
  - rewrite (big_sepM_fn_insert (λ _ _ P',  _ ∗ _ _ P' ∗ _ _ (_ _ P')))%I //.
    iFrame; eauto.
Qed.

Lemma box_delete_empty E f P Q γ :
  ↑N ⊆ E →
  f !! γ = Some false →
  slice N γ Q -∗ ▷ box N f P ={E}=∗ ∃ P',
    ▷ ▷ (P ≡ (Q ∗ P')) ∗ ▷ box N (delete γ f) P'.
Proof.
  iIntros (??) "[#HγQ Hinv] H". iDestruct "H" as (Φ) "[#HeqP Hf]".
  iExists ([∗ map] γ'↦_ ∈ delete γ f, Φ γ')%I.
  iInv N as (b) "[Hγ _]" "Hclose".
  iApply fupd_trans_frame; iFrame "Hclose"; iModIntro; iNext.
  iDestruct (big_sepM_delete _ f _ false with "Hf")
    as "[[Hγ' #[HγΦ ?]] ?]"; first done.
  iDestruct (box_own_agree γ Q (Φ γ) with "[#]") as "HeqQ"; first by eauto.
  iDestruct (box_own_auth_agree γ b false with "[-]") as %->; first by iFrame.
  iSplitL "Hγ"; last iSplit.
  - iExists false; eauto.
  - iNext. iRewrite "HeqP". iRewrite "HeqQ". by rewrite -big_sepM_delete.
  - iExists Φ; eauto.
Qed.

Lemma box_fill E f γ P Q :
  ↑N ⊆ E →
  f !! γ = Some false →
  slice N γ Q -∗ ▷ Q -∗ ▷ box N f P ={E}=∗ ▷ box N (<[γ:=true]> f) P.
Proof.
  iIntros (??) "#[HγQ Hinv] HQ H"; iDestruct "H" as (Φ) "[#HeqP Hf]".
  iInv N as (b') "[>Hγ _]" "Hclose".
  iDestruct (big_sepM_later _ f with "Hf") as "Hf".
  iDestruct (big_sepM_delete _ f _ false with "Hf")
    as "[[>Hγ' #[HγΦ Hinv']] ?]"; first done.
  iMod (box_own_auth_update γ b' false true with "[Hγ Hγ']")
    as "[Hγ Hγ']"; first by iFrame.
  iMod ("Hclose" with "[Hγ HQ]"); first (iNext; iExists true; by iFrame).
  iModIntro; iNext; iExists Φ; iSplit.
  - by rewrite big_sepM_insert_override.
  - rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    iFrame; eauto.
Qed.

Lemma box_empty E f P Q γ :
  ↑N ⊆ E →
  f !! γ = Some true →
  slice N γ Q -∗ ▷ box N f P ={E}=∗ ▷ Q ∗ ▷ box N (<[γ:=false]> f) P.
Proof.
  iIntros (??) "#[HγQ Hinv] H"; iDestruct "H" as (Φ) "[#HeqP Hf]".
  iInv N as (b) "[>Hγ HQ]" "Hclose".
  iDestruct (big_sepM_later _ f with "Hf") as "Hf".
  iDestruct (big_sepM_delete _ f with "Hf")
    as "[[>Hγ' #[HγΦ Hinv']] ?]"; first done.
  iDestruct (box_own_auth_agree γ b true with "[-]") as %->; first by iFrame.
  iFrame "HQ".
  iMod (box_own_auth_update γ with "[Hγ Hγ']") as "[Hγ Hγ']"; first by iFrame.
  iMod ("Hclose" with "[Hγ]"); first (iNext; iExists false; by repeat iSplit).
  iModIntro; iNext; iExists Φ; iSplit.
  - by rewrite big_sepM_insert_override.
  - rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    iFrame; eauto.
Qed.

Lemma box_insert_full Q E f P :
  ↑N ⊆ E →
  ▷ Q -∗ ▷ box N f P ={E}=∗ ∃ γ, ⌜f !! γ = None⌝ ∗
    slice N γ Q ∗ ▷ box N (<[γ:=true]> f) (Q ∗ P).
Proof.
  iIntros (?) "HQ Hbox".
  iMod (box_insert_empty with "Hbox") as (γ) "(% & #Hslice & Hbox)".
  iExists γ. iFrame "%#". iMod (box_fill with "Hslice HQ Hbox"); first done.
  by apply lookup_insert. by rewrite insert_insert.
Qed.

Lemma box_delete_full E f P Q γ :
  ↑N ⊆ E →
  f !! γ = Some true →
  slice N γ Q -∗ ▷ box N f P ={E}=∗
  ∃ P', ▷ Q ∗ ▷ ▷ (P ≡ (Q ∗ P')) ∗ ▷ box N (delete γ f) P'.
Proof.
  iIntros (??) "#Hslice Hbox".
  iMod (box_empty with "Hslice Hbox") as "[$ Hbox]"; try done.
  iMod (box_delete_empty with "Hslice Hbox") as (P') "[Heq Hbox]".
    done. by apply lookup_insert.
  iExists P'. iFrame. rewrite -insert_delete delete_insert ?lookup_delete //.
Qed.

Lemma box_fill_all E f P :
  ↑N ⊆ E →
  box N f P -∗ ▷ P ={E}=∗ box N (const true <$> f) P.
Proof.
  iIntros (?) "H HP"; iDestruct "H" as (Φ) "[#HeqP Hf]".
  iExists Φ; iSplitR; first by rewrite big_sepM_fmap.
  rewrite internal_eq_iff later_iff big_sepM_later.
  iDestruct ("HeqP" with "HP") as "HP".
  iCombine "Hf" "HP" as "Hf".
  rewrite big_sepM_fmap; iApply (fupd_big_sepM _ _ f).
  iApply (big_sepM_impl _ _ f); iFrame "Hf".
  iAlways; iIntros (γ b' ?) "[(Hγ' & #$ & #$) HΦ]".
  iInv N as (b) "[>Hγ _]" "Hclose".
  iMod (box_own_auth_update γ with "[Hγ Hγ']") as "[Hγ $]"; first by iFrame.
  iApply "Hclose". iNext; iExists true. by iFrame.
Qed.

Lemma box_empty_all E f P :
  ↑N ⊆ E →
  map_Forall (λ _, (true =)) f →
  box N f P ={E}=∗ ▷ P ∗ box N (const false <$> f) P.
Proof.
  iDestruct 1 as (Φ) "[#HeqP Hf]".
  iAssert ([∗ map] γ↦b ∈ f, ▷ Φ γ ∗ box_own_auth γ (◯ Excl' false) ∗
    box_own_prop γ (Φ γ) ∗ inv N (slice_inv γ (Φ γ)))%I with ">[Hf]" as "[HΦ ?]".
  { iApply (fupd_big_sepM _ _ f); iApply (big_sepM_impl _ _ f); iFrame "Hf".
    iAlways; iIntros (γ b ?) "(Hγ' & #HγΦ & #Hinv)".
    assert (true = b) as <- by eauto.
    iInv N as (b) "[>Hγ HΦ]" "Hclose".
    iDestruct (box_own_auth_agree γ b true with "[-]") as %->; first by iFrame.
    iMod (box_own_auth_update γ true true false with "[Hγ Hγ']")
      as "[Hγ $]"; first by iFrame.
    iMod ("Hclose" with "[Hγ]"); first (iNext; iExists false; iFrame; eauto).
    iFrame "HγΦ Hinv". by iApply "HΦ". }
  iModIntro; iSplitL "HΦ".
  - rewrite internal_eq_iff later_iff big_sepM_later. by iApply "HeqP".
  - iExists Φ; iSplit; by rewrite big_sepM_fmap.
Qed.

Lemma box_split E f P Q1 Q2 γ b :
  ↑N ⊆ E → f !! γ = Some b →
  slice N γ (Q1 ∗ Q2) -∗ ▷ box N f P ={E}=∗ ∃ γ1 γ2,
    ⌜delete γ f !! γ1 = None⌝ ∗ ⌜delete γ f !! γ2 = None⌝ ∗
    slice N γ1 Q1 ∗ slice N γ2 Q2 ∗ ▷ box N (<[γ2 := b]>(<[γ1 := b]>(delete γ f))) P.
Proof.
  iIntros (??) "#Hslice Hbox". destruct b.
  - iMod (box_delete_full with "Hslice Hbox") as (P') "([HQ1 HQ2] & Heq & Hbox)"; try done.
    iMod (box_insert_full Q1 with "HQ1 Hbox") as (γ1) "(% & #Hslice1 & Hbox)". done.
    iMod (box_insert_full Q2 with "HQ2 Hbox") as (γ2) "(% & #Hslice2 & Hbox)". done.
    iExists γ1, γ2. iFrame "%#". iModIntro. iSplit.
    { iPureIntro. by eapply lookup_insert_None. }
    iNext. eapply internal_eq_rewrite_contractive; [by apply _| |by eauto].
    iNext. iRewrite "Heq". iPureIntro. rewrite assoc. f_equiv. by rewrite comm. done.
  - iMod (box_delete_empty with "Hslice Hbox") as (P') "[Heq Hbox]"; try done.
    iMod (box_insert_empty Q1 with "Hbox") as (γ1) "(% & #Hslice1 & Hbox)".
    iMod (box_insert_empty Q2 with "Hbox") as (γ2) "(% & #Hslice2 & Hbox)".
    iExists γ1, γ2. iFrame "%#". iModIntro. iSplit.
    { iPureIntro. by eapply lookup_insert_None. }
    iNext. eapply internal_eq_rewrite_contractive; [by apply _| |by eauto].
    iNext. iRewrite "Heq". iPureIntro. rewrite assoc. f_equiv. by rewrite comm. done.
Qed.

Lemma box_combine E f P Q1 Q2 γ1 γ2 b :
  ↑N ⊆ E → γ1 ≠ γ2 → f !! γ1 = Some b → f !! γ2 = Some b →
  slice N γ1 Q1 -∗ slice N γ2 Q2 -∗ ▷ box N f P ={E}=∗ ∃ γ,
    ⌜delete γ2 (delete γ1 f) !! γ = None⌝ ∗ slice N γ (Q1 ∗ Q2) ∗
    ▷ box N (<[γ := b]>(delete γ2 (delete γ1 f))) P.
Proof.
  iIntros (????) "#Hslice1 #Hslice2 Hbox". destruct b.
  - iMod (box_delete_full with "Hslice1 Hbox") as (P1) "(HQ1 & Heq1 & Hbox)"; try done.
    iMod (box_delete_full with "Hslice2 Hbox") as (P2) "(HQ2 & Heq2 & Hbox)".
      done. by simplify_map_eq.
    iMod (box_insert_full (Q1 ∗ Q2)%I with "[$HQ1 $HQ2] Hbox")
        as (γ) "(% & #Hslice & Hbox)". done.
    iExists γ. iFrame "%#". iModIntro. iNext.
    eapply internal_eq_rewrite_contractive; [by apply _| |by eauto].
    iNext. iRewrite "Heq1". iRewrite "Heq2". by rewrite assoc.
  - iMod (box_delete_empty with "Hslice1 Hbox") as (P1) "(Heq1 & Hbox)"; try done.
    iMod (box_delete_empty with "Hslice2 Hbox") as (P2) "(Heq2 & Hbox)".
      done. by simplify_map_eq.
    iMod (box_insert_empty (Q1 ∗ Q2)%I with "Hbox") as (γ) "(% & #Hslice & Hbox)".
    iExists γ. iFrame "%#". iModIntro. iNext.
    eapply internal_eq_rewrite_contractive; [by apply _| |by eauto].
    iNext. iRewrite "Heq1". iRewrite "Heq2". by rewrite assoc.
Qed.
End box.

Typeclasses Opaque slice box.
