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

Definition array_init_loop : val :=
  rec: "loop" "src" "i" "n" "f" :=
    if: "i" = "n" then #()
    else "src" +ₗ "i" <- "f" "i";;
         "loop" "src" ("i" + #1) "n" "f".

(* similar to [Array.init] in OCaml's stdlib *)
Definition array_init : val :=
  λ: "n" "f",
    let: "src" := AllocN "n" #() in
    array_init_loop "src" #0 "n" "f";;
    "src".

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

  (* TODO: move to std++? *)
  Lemma insert_0_replicate {A : Type} (x y : A) n :
    <[0:=y]>(replicate (S n) x) = y :: replicate n x.
  Proof. by induction n; eauto. Qed.

  Lemma wp_array_init_loop {A : Type} (g : A → val) (Q : nat → A → iProp Σ)
          (xs : list A) i n l (f : val) stk E :
    (0 < n) →
    length xs = i →
    (i ≤ n) →
    ([∗ list] k↦x∈xs, Q k x) -∗
    (□ ∀ i : nat, WP f #i @ stk; E {{ v, ∃ x : A, ⌜v = g x⌝ ∗ Q i x }}) -∗
    l ↦∗ ((g <$> xs) ++ replicate (n - i) #()) -∗
    WP array_init_loop #l #i #n f @ stk; E {{ _, ∃ ys,
       l ↦∗ (g <$> (xs ++ ys)) ∗ ⌜length (xs++ys) = n⌝ ∗ ([∗ list] k↦x∈(xs++ys), Q k x) }}.
  Proof.
    iIntros (Hn Hxs Hi) "Hxs #Hf Hl". iRevert (Hxs Hi).
    iLöb as "IH" forall (xs i). iIntros (Hxs Hi).
    wp_rec. wp_pures. case_bool_decide; simplify_eq/=; wp_pures.
    - iExists []. iFrame.
      assert (length xs - length xs = 0) as -> by lia.
      rewrite !app_nil_r. eauto with iFrame.
    - wp_bind (f #(length xs)). iApply (wp_wand with "Hf").
      iIntros (v). iDestruct 1 as (x) "[-> Hx]".
      wp_apply (wp_store_offset with "Hl").
      { apply lookup_lt_is_Some_2.
        rewrite app_length.
        assert (length xs ≠ n) by naive_solver.
        assert (n - length xs > 0) by lia.
        rewrite fmap_length replicate_length. lia. }
      iIntros "Hl". wp_pures.
      assert ((Z.of_nat (length xs) + 1)%Z = Z.of_nat (length xs + 1)) as -> by lia.
      iSpecialize ("IH" $! (xs++[x]) (length xs + 1) with "[Hx Hxs] [Hl] [%] [%]").
      { rewrite big_sepL_app /= Nat.add_0_r. by iFrame. }
      { assert (length xs = length xs + 0) as Hlen1 by lia.
        rewrite {1}Hlen1.
        rewrite -{1}(fmap_length g xs).
        rewrite insert_app_r fmap_app /=.
        rewrite app_assoc_reverse /=.
        assert (length xs ≠ n) by naive_solver.
        assert ((n - length xs) = S (n - (length xs + 1))) as -> by lia.
        by rewrite insert_0_replicate. }
      { by rewrite app_length. }
      { assert (length xs ≠ n) by naive_solver. lia. }
      iApply (wp_wand with "IH").
      iIntros (_). iDestruct 1 as (ys) "(Hys & Hlen & HQs)".
      iDestruct "Hlen" as %Hlen.
      rewrite -app_assoc.
      iExists ([x] ++ ys). iFrame. iPureIntro.
      by rewrite app_assoc.
  Qed.

  Theorem wp_array_init {A : Type} (g : A → val) (Q : nat → A → iProp Σ)
          n (f : val) stk E :
    (0 < n)%Z →
    {{{ (□ ∀ i : nat, WP f #i @ stk; E {{ v, ∃ x : A, ⌜v = g x⌝ ∗ Q i x }}) }}}
      array_init #n f @ stk; E
    {{{ l xs, RET #l; l ↦∗ (g<$>xs) ∗ ⌜Z.of_nat (length xs) = n⌝ ∗ ([∗ list] k↦x∈xs, Q k x) }}}.
  Proof.
    intros Hn. iIntros (Φ) "#Hf HΦ".
    wp_rec. wp_pures. wp_alloc l as "Hl"; first done.
    wp_pures.
    iPoseProof (wp_array_init_loop g Q [] 0 (Z.to_nat n) with "[//] Hf [Hl]") as "H"; try by (simpl; lia).
    { simpl. assert (Z.to_nat n - 0 = Z.to_nat n) as -> by lia. done. }
    assert (Z.of_nat 0%nat = 0%Z) as -> by lia.
    assert (Z.of_nat (Z.to_nat n) = n) as -> by lia.
    wp_apply (wp_wand with "H").
    iIntros (?). iDestruct 1 as (vs) "(Hl & % & HQs)".
    wp_pures. iApply "HΦ".
    iFrame "Hl HQs". iPureIntro. lia.
  Qed.

  Lemma wp_array_init' (Q : nat → val → iProp Σ) n (f : val) stk E :
    (0 < n)%Z →
    {{{ (□ ∀ i : nat, WP f #i @ stk; E {{ v, Q i v }}) }}}
      array_init #n f @ stk; E
    {{{ l xs, RET #l; l ↦∗ xs ∗ ⌜Z.of_nat (length xs) = n⌝ ∗ ([∗ list] k↦x∈xs, Q k x) }}}.
  Proof.
    intros Hn. iIntros (Φ) "#Hf HΦ".
    iApply (wp_array_init id Q with "[Hf]"); try done.
    { iModIntro. iIntros (i). iApply (wp_wand with "Hf").
      iIntros (v) "Hv". iExists v; eauto with iFrame. }
    iNext. iIntros (l xs). by rewrite list_fmap_id.
  Qed.

End proof.
