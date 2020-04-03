From iris.algebra Require Import auth excl gmap.
From iris.base_logic.lib Require Import own invariants gen_heap.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

(** A "GC" location is a location that can never be deallocated explicitly by
the program.  It provides a persistent witness that will always allow reading
the location.  The location is moreover associated with a (pure, Coq-level)
invariant determining which values are allowed to be stored in that location.
The persistent witness cannot know the exact value that will be read, but it
*can* know that the value satisfies the invariant.

This is useful for data structures like RDCSS that need to read locations long
after their ownership has been passed back to the client, but do not care *what*
it is that they are reading in that case.

Note that heap_lang does not actually have explicit dealloaction. However, the
proof rules we provide for heap operations currently are conservative in the
sense that they do not expose this fact.  By making "GC" locations a separate
assertion, we can keep all the other proofs that do not need it conservative.
*)

Definition gcN: namespace := nroot .@ "gc".
Local Notation "l ↦ v" := (mapsto l 1 v) (at level 20) : bi_scope.

Definition gc_mapUR (L V : Type) `{Countable L} : ucmraT := gmapUR L $ prodR
  (optionR $ exclR $ leibnizO V)
  (agreeR (V -d> PropO)).

Definition to_gc_map {L V : Type} `{Countable L} (gcm: gmap L (V * (V -d> PropO))) : gc_mapUR L V :=
  prod_map (λ x, Excl' x) to_agree <$> gcm.

Class gcG (L V : Type) (Σ : gFunctors) `{Countable L} := GcG {
  gc_inG :> inG Σ (authR (gc_mapUR L V));
  gc_name : gname
}.
Arguments GcG _ _ {_ _ _ _}.
Arguments gc_name {_ _ _ _ _} _ : assert.

Class gcPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gc_preG_inG :> inG Σ (authR (gc_mapUR L V))
}.

Definition gcΣ (L V : Type) `{Countable L} : gFunctors :=
  #[ GFunctor (authR (gc_mapUR L V)) ].

Instance subG_gcPreG (L V : Type) `{Countable L} {Σ} :
  subG (gcΣ L V) Σ → gcPreG L V Σ.
Proof. solve_inG. Qed.

Section defs.
  Context {L V : Type} `{Countable L}.
  Context `{!invG Σ, !gen_heapG L V Σ, gG: !gcG L V Σ}.

  Definition gc_inv_P : iProp Σ :=
    (∃ gcm : gmap L (V * (V -d> PropO)),
        own (gc_name gG) (● to_gc_map gcm) ∗ [∗ map] l ↦ p ∈ gcm, ⌜p.2 p.1⌝ ∗ l ↦ p.1)%I.

  Definition gc_inv : iProp Σ := inv gcN gc_inv_P.

  Definition gc_mapsto (l : L) (v : V) (I : V → Prop) : iProp Σ :=
    own (gc_name gG) (◯ {[l := (Excl' v, to_agree I)]}).

  Definition is_gc_loc (l : L) (I : V → Prop) : iProp Σ :=
    own (gc_name gG) (◯ {[l := (None, to_agree I)]}).

End defs.

(* [gc_inv] has no parameters to infer the types from, so we need to
   make them explicit. *)
Arguments gc_inv _ _ {_ _ _ _ _ _}.

Section to_gc_map.
  Context {L V : Type} `{Countable L}.
  Implicit Types (gcm : gmap L (V * (V -d> PropO))).

  Lemma to_gc_map_valid gcm : ✓ to_gc_map gcm.
  Proof. intros l. rewrite lookup_fmap. by case (gcm !! l). Qed.

  Lemma to_gc_map_singleton l v I :
    to_gc_map {[l := (v, I)]} =@{gc_mapUR L V} {[l := (Excl' v, to_agree I)]}.
  Proof. by rewrite /to_gc_map fmap_insert fmap_empty. Qed.

  Lemma to_gc_map_insert l v I gcm :
    to_gc_map (<[l := (v, I)]> gcm) = <[l := (Excl' v, to_agree I)]> (to_gc_map gcm).
  Proof. by rewrite /to_gc_map fmap_insert. Qed.

  Lemma lookup_to_gc_map_None gcm l :
    gcm !! l = None → to_gc_map gcm !! l = None.
  Proof. by rewrite /to_gc_map lookup_fmap=> ->. Qed.

  Lemma lookup_to_gc_map_Some gcm l v I :
    gcm !! l = Some (v, I) → to_gc_map gcm !! l = Some (Excl' v, to_agree I).
  Proof. by rewrite /to_gc_map lookup_fmap=> ->. Qed.

  Lemma lookup_to_gc_map_Some_2 gcm l v' I' :
    to_gc_map gcm !! l ≡ Some (v', I') →
    ∃ v I, v' ≡ Excl' v ∧ I' ≡ to_agree I ∧ gcm !! l = Some (v, I).
  Proof.
    rewrite /to_gc_map /prod_map lookup_fmap. rewrite fmap_Some_equiv.
    intros ([] & Hsome & [Heqv HeqI]). eauto.
  Qed.
End to_gc_map.

Lemma gc_init {L V : Type} `{Countable L, !invG Σ, !gen_heapG L V Σ, !gcPreG L V Σ} E:
  ⊢ |==> ∃ _ : gcG L V Σ, |={E}=> gc_inv L V.
Proof.
  iMod (own_alloc (● (to_gc_map ∅))) as (γ) "H●".
  { rewrite auth_auth_valid. exact: to_gc_map_valid. }
  iModIntro.
  iExists (GcG L V γ).
  iAssert (gc_inv_P (gG := GcG L V γ)) with "[H●]" as "P".
  { iExists _. iFrame. done. }
  iApply (inv_alloc gcN E gc_inv_P with "P").
Qed.

Section gc.
  Context {L V : Type} `{Countable L}.
  Context `{!invG Σ, !gen_heapG L V Σ, gG: !gcG L V Σ}.
  Implicit Types (l : L) (v : V) (I : V → Prop).
  Implicit Types (gcm : gmap L (V * (V -d> PropO))).

  Global Instance is_gc_loc_persistent l I : Persistent (is_gc_loc l I).
  Proof. rewrite /is_gc_loc. apply _. Qed.

  Global Instance is_gc_loc_timeless l I : Timeless (is_gc_loc l I).
  Proof. rewrite /is_gc_loc. apply _. Qed.

  Global Instance gc_mapsto_timeless l v I : Timeless (gc_mapsto l v I).
  Proof. rewrite /is_gc_loc. apply _. Qed.

  Lemma make_gc l v I E :
    ↑gcN ⊆ E →
    I v →
    gc_inv L V -∗ l ↦ v ={E}=∗ gc_mapsto l v I.
  Proof.
    iIntros (HN HI) "#Hinv Hl".
    iMod (inv_acc_timeless _ gcN with "Hinv") as "[HP Hclose]"=>//.
    iDestruct "HP" as (gcm) "[H● HsepM]".
    destruct (gcm !! l) as [v' | ] eqn: Hlookup.
    - (* auth map contains l --> contradiction *)
      iDestruct (big_sepM_lookup with "HsepM") as "[_ Hl']"=>//.
      by iDestruct (mapsto_valid_2 with "Hl Hl'") as %?.
    - iMod (own_update with "H●") as "[H● H◯]".
      { apply lookup_to_gc_map_None in Hlookup.
        apply (auth_update_alloc _ (to_gc_map (<[l := (v, I)]> gcm)) (to_gc_map ({[l := (v, I)]}))).
        rewrite to_gc_map_insert to_gc_map_singleton.
        pose proof (to_gc_map_valid gcm).
        apply: alloc_singleton_local_update; done. }
      iMod ("Hclose" with "[H● HsepM Hl]").
      + iExists _.
        iDestruct (big_sepM_insert with "[HsepM Hl]") as "HsepM"=>//; iFrame.
        auto with iFrame.
      + iModIntro. by rewrite /gc_mapsto to_gc_map_singleton.
  Qed.

  Lemma gc_is_gc l v I : gc_mapsto l v I -∗ is_gc_loc l I.
  Proof.
    iIntros "Hgc_l". rewrite /gc_mapsto /is_gc_loc.
    (* We need to help Coq type inference... *)
    change (V → Prop) with (ofe_car $ leibnizO (V → Prop)) in I.
    (* FIXME: is there any good way to avoid repeating the goal here? *)
    assert (◯ {[l := (Excl' v, to_agree I)]} ≡ ◯ {[l := (Excl' v, to_agree I)]} ⋅ ◯ {[l := (None, to_agree I)]}) as ->.
    { rewrite -auth_frag_op op_singleton -pair_op agree_idemp //. }
    iDestruct "Hgc_l" as "[_ H◯_none]".
    iFrame.
  Qed.

  Lemma is_gc_lookup_Some l gcm I :
    is_gc_loc l I -∗ own (gc_name gG) (● to_gc_map gcm) -∗ ⌜∃ v, gcm !! l ≡ Some (v, I)⌝.
  Proof.
    iIntros "Hgc_l H◯".
    iCombine "H◯ Hgc_l" as "Hcomb".
    iDestruct (own_valid with "Hcomb") as %Hvalid.
    iPureIntro.
    apply auth_both_valid in Hvalid as [Hincluded Hvalid].
    setoid_rewrite singleton_included in Hincluded.
    destruct Hincluded as ([v' I'] & Hsome & Hincl).
    edestruct (@lookup_to_gc_map_Some_2 L V) as [v'' [I'' (_ & HI & Hgcm)]]; first done.
    rewrite ->HI in Hincl. exists v''. rewrite Hgcm. f_equal.
    rewrite ->Some_included_total in Hincl.
    apply pair_included in Hincl. simpl in Hincl.
    destruct Hincl as [_ Hincl%to_agree_included].
    
    fold_leibniz. subst I''. done.
  Qed.

  Lemma gc_mapsto_lookup_Some l v gcm I :
    gc_mapsto l v I -∗ own (gc_name gG) (● to_gc_map gcm) -∗ ⌜ gcm !! l = Some (v, I) ⌝.
  Proof.
    iIntros "Hgc_l H●".
    iCombine "H● Hgc_l" as "Hcomb".
    iDestruct (own_valid with "Hcomb") as %Hvalid.
    iPureIntro.
    apply auth_both_valid in Hvalid as [Hincluded Hvalid].
    setoid_rewrite singleton_included in Hincluded.
    destruct Hincluded as ([v' I'] & Hsome & Hincl).
    edestruct (@lookup_to_gc_map_Some_2 L V) as [v'' [I'' (Hv & HI & ->)]]; first done.
    rewrite ->HI in Hincl. f_equal.
    rewrite ->Some_included_total in Hincl.
    apply pair_included in Hincl. simpl in Hincl.
    destruct Hincl as [Hinclv HinclI%to_agree_included].
    move:Hinclv. rewrite ->Hv. move=>/Excl_included ?.
    fold_leibniz. simplify_eq. done.
  Qed.

  (** An accessor to make use of [gc_mapsto].
    This opens the invariant *before* consuming [gc_mapsto] so that you can use
    this before opening an atomic update that provides [gc_mapsto]!. *)
  Lemma gc_acc_strong E :
    ↑gcN ⊆ E →
    gc_inv L V ={E, E ∖ ↑gcN}=∗ ∀ l v I, gc_mapsto l v I -∗
      (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗ gc_mapsto l w I ∗ |={E ∖ ↑gcN, E}=> True)).
  Proof.
    iIntros (HN) "#Hinv".
    iMod (inv_acc_timeless _ gcN _ with "Hinv") as "[HP Hclose]"=>//.
    iIntros "!>" (l v I) "Hgc_l".
    iDestruct "HP" as (gcm) "[H● HsepM]".
    iDestruct (gc_mapsto_lookup_Some with "Hgc_l H●") as %Hsome.
    iDestruct (big_sepM_delete with "HsepM") as "[[HI Hl] HsepM]"=>//=.
    iFrame. iIntros (w) "% Hl".
    iMod (own_update_2 with "H● Hgc_l") as "[H● H◯]".
    { apply (auth_update _ _ (<[l := (Excl' w, to_agree I)]> (to_gc_map gcm))
             {[l := (Excl' w, to_agree I)]}).
      apply: singleton_local_update.
      { by apply lookup_to_gc_map_Some in Hsome. }
      apply: prod_local_update_1.  apply: option_local_update.
      apply: exclusive_local_update. done. }
    iDestruct (big_sepM_insert _ _ _ (w, I) with "[$HsepM $Hl //]") as "HsepM".
    { apply lookup_delete. }
    rewrite insert_delete -to_gc_map_insert. iModIntro. iFrame.
    iMod ("Hclose" with "[H● HsepM]"); [ iExists _; by iFrame | by iModIntro].
  Qed.

  (** Derive a more standard accessor. *)
  Lemma gc_acc E l v I:
    ↑gcN ⊆ E →
    gc_inv L V -∗ gc_mapsto l v I ={E, E ∖ ↑gcN}=∗
      (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑gcN, E}=∗ gc_mapsto l w I)).
  Proof.
    iIntros (HN) "#Hinv Hl".
    iMod (gc_acc_strong with "Hinv") as "Hacc"; first done.
    iDestruct ("Hacc" with "Hl") as "(HI & Hl & Hclose)".
    iModIntro. iFrame. iIntros (w) "HI Hl".
    iMod ("Hclose" with "HI Hl") as "[$ $]".
  Qed.

  Lemma is_gc_access l I E :
    ↑gcN ⊆ E →
    gc_inv L V -∗ is_gc_loc l I ={E, E ∖ ↑gcN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑gcN, E}=∗ ⌜True⌝).
  Proof.
    iIntros (HN) "#Hinv Hgc_l".
    iMod (inv_acc_timeless _ gcN _ with "Hinv") as "[HP Hclose]"=>//.
    iModIntro.
    iDestruct "HP" as (gcm) "[H● HsepM]".
    iDestruct (is_gc_lookup_Some with "Hgc_l H●") as %[v Hsome].
    iDestruct (big_sepM_lookup_acc with "HsepM") as "[[#HI Hl] HsepM]"=>//.
    iExists _. iFrame "∗#".
    iIntros "Hl".
    iMod ("Hclose" with "[H● HsepM Hl]"); last done.
    iExists _. iFrame.
    iApply ("HsepM" with "[$Hl //]").
  Qed.

End gc.

Typeclasses Opaque is_gc_loc gc_mapsto.
