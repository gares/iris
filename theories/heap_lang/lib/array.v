From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import proofmode notation.
From iris Require Import options.

(** Provides some array utilities:

* [array_free], to deallocate an entire array in one go.
* [array_copy_to], a function which copies to an array in-place.
* Using [array_copy_to] we also implement [array_clone], which allocates a fresh
array and copies to it.

*)

Definition array_free : val :=
  rec: "freeN" "ptr" "n" :=
    if: "n" ≤ #0 then #()
    else Free "ptr";;
         "freeN" ("ptr" +ₗ #1) ("n" - #1).

Definition array_copy_to : val :=
  rec: "array_copy_to" "dst" "src" "n" :=
    if: "n" ≤ #0 then #()
    else "dst" <- !"src";;
         "array_copy_to" ("dst" +ₗ #1) ("src" +ₗ #1) ("n" - #1).

Definition array_clone : val :=
  λ: "src" "n",
    let: "dst" := AllocN "n" #() in
    array_copy_to "dst" "src" "n";;
    "dst".

Section proof.
  Context `{!heapG Σ}.

  Lemma twp_array_free s E l vs (n : Z) :
    n = length vs →
    [[{ l ↦∗ vs }]] array_free #l #n @ s; E [[{ RET #(); True }]].
  Proof.
    iIntros (Hlen Φ) "Hl HΦ".
    iInduction vs as [|v vs] "IH" forall (l n Hlen); subst n; wp_rec; wp_pures.
    { iApply "HΦ". done. }
    iDestruct (array_cons with "Hl") as "[Hv Hl]".
    wp_free. wp_pures. iApply ("IH" with "[] Hl"); eauto with lia.
  Qed.
  Lemma wp_array_free s E l vs (n : Z) :
    n = length vs →
    {{{ l ↦∗ vs }}} array_free #l #n @ s; E {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_free with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Theorem twp_array_copy_to stk E (dst src : loc) vdst vsrc q (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
    [[{ dst ↦∗ vdst ∗ src ↦∗{q} vsrc }]]
      array_copy_to #dst #src #n @ stk; E
    [[{ RET #(); dst ↦∗ vsrc ∗ src ↦∗{q} vsrc }]].
  Proof.
    iIntros (Hvdst Hvsrc Φ) "[Hdst Hsrc] HΦ".
    iInduction vdst as [|v1 vdst] "IH" forall (n dst src vsrc Hvdst Hvsrc);
      destruct vsrc as [|v2 vsrc]; simplify_eq/=; try lia; wp_rec; wp_pures.
    { iApply "HΦ". iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv1 Hdst]".
    iDestruct (array_cons with "Hsrc") as "[Hv2 Hsrc]".
    wp_load; wp_store.
    wp_apply ("IH" with "[%] [%] Hdst Hsrc"); [ lia .. | ].
    iIntros "[Hvdst Hvsrc]".
    iApply "HΦ"; by iFrame.
  Qed.
  Theorem wp_array_copy_to stk E (dst src : loc) vdst vsrc q (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
    {{{ dst ↦∗ vdst ∗ src ↦∗{q} vsrc }}}
      array_copy_to #dst #src #n @ stk; E
    {{{ RET #(); dst ↦∗ vsrc ∗ src ↦∗{q} vsrc }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_copy_to with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Theorem twp_array_clone stk E l q vl n :
    Z.of_nat (length vl) = n →
    (0 < n)%Z →
    [[{ l ↦∗{q} vl }]]
      array_clone #l #n @ stk; E
    [[{ l', RET #l'; l' ↦∗ vl ∗ l ↦∗{q} vl }]].
  Proof.
    iIntros (Hvl Hn Φ) "Hvl HΦ".
    wp_lam.
    wp_alloc dst as "Hdst"; first by auto.
    wp_apply (twp_array_copy_to with "[$Hdst $Hvl]").
    - rewrite replicate_length Z2Nat.id; lia.
    - auto.
    - iIntros "[Hdst Hl]".
      wp_pures.
      iApply "HΦ"; by iFrame.
  Qed.
  Theorem wp_array_clone stk E l q vl n :
    Z.of_nat (length vl) = n →
    (0 < n)%Z →
    {{{ l ↦∗{q} vl }}}
      array_clone #l #n @ stk; E
    {{{ l', RET #l'; l' ↦∗ vl ∗ l ↦∗{q} vl }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_clone with "H"); [auto..|]; iIntros (l') "H HΦ". by iApply "HΦ".
  Qed.

End proof.
