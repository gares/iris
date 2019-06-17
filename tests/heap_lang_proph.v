From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Import lang adequacy proofmode notation.
From iris.heap_lang Require Import lang.
Set Default Proof Using "Type".

Section tests.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Definition CAS_resolve e1 e2 e3 p v :=
    Resolve (CAS e1 e2 e3) p v.

  Lemma wp_cas_suc_resolve s E (l : loc) (p : proph_id) (vs : list (val * val)) (v1 v2 v : val) :
    vals_cas_compare_safe v1 v1 →
    {{{ proph p vs ∗ ▷ l ↦ v1 }}}
      CAS_resolve #l v1 v2 #p v @ s; E
    {{{ RET v1 ; ∃ vs', ⌜vs = (v1, v)::vs'⌝ ∗ proph p vs' ∗ l ↦ v2 }}}.
  Proof.
    iIntros (Hcmp Φ) "[Hp Hl] HΦ".
    wp_apply (wp_resolve with "Hp"); first done.
    assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
    wp_cas_suc. iIntros (vs' ->) "Hp".
    iApply "HΦ". eauto with iFrame.
  Qed.

  Lemma wp_cas_fail_resolve s E (l : loc) (p : proph_id) (vs : list (val * val)) (v' v1 v2 v : val) :
    val_for_compare v' ≠ val_for_compare v1 → vals_cas_compare_safe v' v1 →
    {{{ proph p vs ∗ ▷ l ↦ v' }}}
      CAS_resolve #l v1 v2 #p v @ s; E
    {{{ RET v' ; ∃ vs', ⌜vs = (v', v)::vs'⌝ ∗ proph p vs' ∗ l ↦ v' }}}.
  Proof.
    iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
    wp_apply (wp_resolve with "Hp"); first done.
    wp_cas_fail. iIntros (vs' ->) "Hp".
    iApply "HΦ". eauto with iFrame.
  Qed.

  Lemma test_resolve1 E (l : loc) (n : Z) (p : proph_id) (vs : list (val * val)) (v : val) :
    l ↦ #n -∗
    proph p vs -∗
    WP Resolve (CAS #l #n (#n + #1)) #p v @ E {{ v, ⌜v = #n⌝ ∗ ∃vs, proph p vs ∗ l ↦ #(n+1) }}%I.
  Proof.
    iIntros "Hl Hp". wp_pures. wp_apply (wp_resolve with "Hp"); first done.
    wp_cas_suc. iIntros (ws ->) "Hp". eauto with iFrame.
  Qed.

  Lemma test_resolve2 E (l : loc) (n m : Z) (p : proph_id) (vs : list (val * val)) :
    proph p vs -∗
    WP Resolve (#n + #m - (#n + #m)) #p #() @ E {{ v, ⌜v = #0⌝ ∗ ∃vs, proph p vs }}%I.
  Proof.
    iIntros "Hp". wp_pures. wp_apply (wp_resolve with "Hp"); first done.
    wp_pures. iIntros (ws ->) "Hp". rewrite Z.sub_diag. eauto with iFrame.
  Qed.

  Lemma test_resolve3 s E (p1 p2 : proph_id) (vs1 vs2 : list (val * val)) (n : Z) :
    {{{ proph p1 vs1 ∗ proph p2 vs2 }}}
      Resolve (Resolve (#n - #n) #p2 #2) #p1 #1 @ s; E
    {{{ RET #0 ; ∃ vs1' vs2', ⌜vs1 = (#0, #1)::vs1' ∧ vs2 = (#0, #2)::vs2'⌝ ∗ proph p1 vs1' ∗ proph p2 vs2' }}}.
  Proof.
    iIntros (Φ) "[Hp1 Hp2] HΦ".
    wp_apply (wp_resolve with "Hp1"); first done.
    wp_apply (wp_resolve with "Hp2"); first done.
    wp_op.
    iIntros (vs2' ->) "Hp2". iIntros (vs1' ->) "Hp1". rewrite Z.sub_diag.
    iApply "HΦ". iExists vs1', vs2'. eauto with iFrame.
  Qed.

  Lemma test_resolve4 s E (p1 p2 : proph_id) (vs1 vs2 : list (val * val)) (n : Z) :
    {{{ proph p1 vs1 ∗ proph p2 vs2 }}}
      Resolve (Resolve (#n - #n) ((λ: "x", "x") #p2) (#0 + #2)) ((λ: "x", "x") #p1) (#0 + #1) @ s; E
    {{{ RET #0 ; ∃ vs1' vs2', ⌜vs1 = (#0, #1)::vs1' ∧ vs2 = (#0, #2)::vs2'⌝ ∗ proph p1 vs1' ∗ proph p2 vs2' }}}.
  Proof.
    iIntros (Φ) "[Hp1 Hp2] HΦ".
    wp_apply (wp_resolve with "Hp1"); first done.
    wp_apply (wp_resolve with "Hp2"); first done.
    wp_op.
    iIntros (vs2' ->) "Hp2". iIntros (vs1' ->) "Hp1". rewrite Z.sub_diag.
    iApply "HΦ". iExists vs1', vs2'. eauto with iFrame.
  Qed.

End tests.
