From iris.algebra Require Import auth excl gmap.
From iris.base_logic.lib Require Export own invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export lang locations lifting.
Set Default Proof Using "Type".
Import uPred.

(** A "GC" location is a location that can never be deallocated explicitly by
the program.  It provides a persistent witness that wuill always allow reading
the location, albeit with no way to predict what is going to be read.  This is
useful for data structures like RDCSS that need to read locations long after
their ownership has been passed back to the client, but do not care *what* it is
that they are reading in that case.

Note that heap_lang does not actually have explicit dealloaction. However, the
proof rules we provide for heap operations currently are conservative in the
sense that they do not expose this fact.  By making "GC" locations a separate
assertion, we can keep all the other proofs that do not need it conservative.
*)

Definition gcN: namespace := nroot .@ "gc".

Definition gc_mapUR : ucmraT := gmapUR loc $ optionR $ exclR $ valO.

Definition to_gc_map (gcm: gmap loc val) : gc_mapUR := (λ v : val, Excl' v) <$> gcm.

Class gcG  (Σ : gFunctors) := GcG {
  gc_inG :> inG Σ (authR (gc_mapUR));
  gc_name : gname
}.

Arguments gc_name {_} _ : assert.

Class gcPreG (Σ : gFunctors) := {
  gc_preG_inG :> inG Σ (authR (gc_mapUR))
}.

Definition gcΣ : gFunctors :=
  #[ GFunctor (authR (gc_mapUR)) ].

Instance subG_gcPreG {Σ} : subG gcΣ Σ → gcPreG Σ.
Proof. solve_inG. Qed.

Section defs.

  Context `{!invG Σ, !heapG Σ, gG: gcG Σ}.

  Definition gc_inv_P: iProp Σ := 
    ((∃(gcm: gmap loc val), own (gc_name gG) (● to_gc_map gcm) ∗ ([∗ map] l ↦ v ∈ gcm, (l ↦ v)) ) )%I.

  Definition gc_inv : iProp Σ := inv gcN gc_inv_P.

  Definition gc_mapsto (l: loc) (v: val) : iProp Σ := own (gc_name gG) (◯ {[l := Excl' v]}).

  Definition is_gc_loc (l: loc) : iProp Σ := own (gc_name gG) (◯ {[l := None]}).

End defs.

Section to_gc_map.

  Lemma to_gc_map_valid gcm: ✓ to_gc_map gcm.
  Proof. intros l. rewrite lookup_fmap. by case (gcm !! l). Qed.

  Lemma to_gc_map_empty: to_gc_map ∅ = ∅.
  Proof. by rewrite /to_gc_map fmap_empty. Qed.

  Lemma to_gc_map_singleton l v: to_gc_map {[l := v]} = {[l :=  Excl' v]}.
  Proof. by rewrite /to_gc_map fmap_insert fmap_empty. Qed.

  Lemma to_gc_map_insert l v gcm:
    to_gc_map (<[l := v]> gcm) = <[l := Excl' v]> (to_gc_map gcm).
  Proof. by rewrite /to_gc_map fmap_insert. Qed.

  Lemma to_gc_map_delete l gcm :
    to_gc_map (delete l gcm) = delete l (to_gc_map gcm).
  Proof. by rewrite /to_gc_map fmap_delete. Qed.

  Lemma lookup_to_gc_map_None gcm l :
    gcm !! l = None → to_gc_map gcm !! l = None.
  Proof. by rewrite /to_gc_map lookup_fmap=> ->. Qed.

  Lemma lookup_to_gc_map_Some gcm l v :
    gcm !! l = Some v → to_gc_map gcm !! l = Some (Excl' v).
  Proof. by rewrite /to_gc_map lookup_fmap=> ->. Qed.


  Lemma lookup_to_gc_map_Some_2 gcm l w :
    to_gc_map gcm !! l = Some w → ∃ v, gcm !! l = Some v.
  Proof.
    rewrite /to_gc_map lookup_fmap. rewrite fmap_Some.
    intros (x & Hsome & Heq). eauto.
  Qed.

  Lemma lookup_to_gc_map_Some_3 gcm l w :
    to_gc_map gcm !! l = Some (Excl' w) → gcm !! l = Some w.
  Proof.
    rewrite /to_gc_map lookup_fmap. rewrite fmap_Some.
    intros (x & Hsome & Heq). by inversion Heq.
  Qed.

  Lemma excl_option_included (v: val) y:
    ✓ y → Excl' v ≼ y → y = Excl' v.
  Proof.
    intros ? H. destruct y.
    - apply Some_included_exclusive in H;[ | apply _ | done ].
      setoid_rewrite leibniz_equiv_iff in H.
      by rewrite H.
    - apply is_Some_included in H.
      + by inversion H.
      + by eapply mk_is_Some.
  Qed.

  Lemma gc_map_singleton_included gcm l v :
    {[l := Some (Excl v)]} ≼ to_gc_map gcm → gcm !! l = Some v.
  Proof.
    rewrite singleton_included.
    setoid_rewrite Some_included_total.
    intros (y & Hsome & Hincluded).
    pose proof (lookup_valid_Some _ _ _ (to_gc_map_valid gcm) Hsome) as Hvalid.
    pose proof (excl_option_included _ _ Hvalid Hincluded) as Heq.
    rewrite Heq in Hsome.
    apply lookup_to_gc_map_Some_3.
    by setoid_rewrite leibniz_equiv_iff in Hsome.
  Qed.
End to_gc_map.

Lemma gc_init `{!invG Σ, !heapG Σ, !gcPreG Σ} E:
  (|==> ∃ _ : gcG Σ, |={E}=> gc_inv)%I.
Proof.
  iMod (own_alloc (● (to_gc_map ∅))) as (γ) "H●".
  { rewrite auth_auth_valid. exact: to_gc_map_valid. }
  iModIntro.
  iExists (GcG Σ _ γ).
  iAssert (gc_inv_P (gG := GcG Σ _ γ)) with "[H●]" as "P". 
  {
    iExists _. iFrame.
    by iApply big_sepM_empty.
  }
  iMod ((inv_alloc gcN E gc_inv_P) with "P") as "#InvGC".
  iModIntro. iFrame "#".
Qed.

Section gc.
  Context `{!invG Σ, !heapG Σ, !gcG Σ}.

  Global Instance is_gc_loc_persistent (l: loc): Persistent (is_gc_loc l).
  Proof. rewrite /is_gc_loc. apply _. Qed.

  Global Instance is_gc_loc_timeless (l: loc): Timeless (is_gc_loc l).
  Proof. rewrite /is_gc_loc. apply _. Qed.

  Global Instance gc_mapsto_timeless (l: loc) (v: val): Timeless (gc_mapsto l v).
  Proof. rewrite /is_gc_loc. apply _. Qed.

  Global Instance gc_inv_P_timeless: Timeless gc_inv_P.
  Proof. rewrite /gc_inv_P. apply _. Qed.

  Lemma make_gc l v E: ↑gcN ⊆ E → gc_inv -∗ l ↦ v ={E}=∗ gc_mapsto l v.
  Proof.
    iIntros (HN) "#Hinv Hl".
    iMod (inv_open_timeless _ gcN _ with "Hinv") as "[P Hclose]"=>//.
    iDestruct "P" as (gcm) "[H● HsepM]".
    destruct (gcm !! l) as [v' | ] eqn: Hlookup.
    - (* auth map contains l --> contradiction *)
      iDestruct (big_sepM_lookup with "HsepM") as "Hl'"=>//.
      by iDestruct (mapsto_valid_2 with "Hl Hl'") as %?.
    - iMod (own_update with "H●") as "[H● H◯]".
      {
        apply lookup_to_gc_map_None in Hlookup.
        apply (auth_update_alloc _ (to_gc_map (<[l := v]> gcm)) (to_gc_map ({[l := v]}))).
        rewrite to_gc_map_insert to_gc_map_singleton.
        pose proof (to_gc_map_valid gcm).
        setoid_rewrite alloc_singleton_local_update=>//.
      }
      iMod ("Hclose" with "[H● HsepM Hl]"). 
      + iExists _.
        iDestruct (big_sepM_insert with "[HsepM Hl]") as "HsepM"=>//; iFrame. iFrame.
      + iModIntro. by rewrite /gc_mapsto to_gc_map_singleton.
  Qed.

  Lemma gc_is_gc l v: gc_mapsto l v -∗ is_gc_loc l.
  Proof.
    iIntros "Hgc_l". rewrite /gc_mapsto.
    assert (Excl' v = (Excl' v) ⋅ None)%I as ->. { done. }
    rewrite -op_singleton auth_frag_op own_op.
    iDestruct "Hgc_l" as "[_ H◯_none]".
    iFrame.
  Qed.

  Lemma is_gc_lookup_Some  l gcm: is_gc_loc l -∗ own (gc_name _) (● to_gc_map gcm) -∗ ⌜∃ v, gcm !! l = Some v⌝.
    iIntros "Hgc_l H◯".
    iCombine "H◯ Hgc_l" as "Hcomb".
    iDestruct (own_valid with "Hcomb") as %Hvalid.
    iPureIntro.
    apply auth_both_valid in Hvalid as [Hincluded Hvalid]. 
    setoid_rewrite singleton_included in Hincluded. 
    destruct Hincluded as (y & Hsome & _).
    eapply lookup_to_gc_map_Some_2.
    by apply leibniz_equiv_iff in Hsome.
  Qed.

  Lemma gc_mapsto_lookup_Some l v gcm: gc_mapsto l v -∗ own (gc_name _) (● to_gc_map gcm) -∗ ⌜ gcm !! l = Some v ⌝.
  Proof.
    iIntros "Hgc_l H●".
    iCombine "H● Hgc_l" as "Hcomb".
    iDestruct (own_valid with "Hcomb") as %Hvalid.
    iPureIntro.
    apply auth_both_valid in Hvalid as [Hincluded Hvalid]. 
    by apply gc_map_singleton_included.
  Qed.

  (** An accessor to make use of [gc_mapsto].
    This opens the invariant *before* consuming [gc_mapsto] so that you can use
    this before opening an atomic update that provides [gc_mapsto]!. *)
  Lemma gc_access E:
    ↑gcN ⊆ E →
    gc_inv ={E, E ∖ ↑gcN}=∗ ∀ l v, gc_mapsto l v -∗
      (l ↦ v ∗ (∀ w, l ↦ w ==∗ gc_mapsto l w ∗ |={E ∖ ↑gcN, E}=> True)).
  Proof.
    iIntros (HN) "#Hinv".
    iMod (inv_open_timeless _ gcN _ with "Hinv") as "[P Hclose]"=>//.
    iIntros "!>" (l v) "Hgc_l".
    iDestruct "P" as (gcm) "[H● HsepM]".
    iDestruct (gc_mapsto_lookup_Some with "Hgc_l H●") as %Hsome.
    iDestruct (big_sepM_delete with "HsepM") as "[Hl HsepM]"=>//. 
    iFrame. iIntros (w) "Hl".
    iMod (own_update_2 with "H● Hgc_l") as "[H● H◯]".
    { apply (auth_update _ _ (<[l := Excl' w]> (to_gc_map gcm)) {[l := Excl' w]}).
      eapply singleton_local_update.
      { by apply lookup_to_gc_map_Some in Hsome. }
      by apply option_local_update, exclusive_local_update.
    }
    iDestruct (big_sepM_insert with "[Hl HsepM]") as "HsepM"; [ | iFrame | ].
    { apply lookup_delete. }
    rewrite insert_delete. rewrite <- to_gc_map_insert.
    iModIntro. iFrame.
    iMod ("Hclose" with "[H● HsepM]"); [ iExists _; by iFrame | by iModIntro].
  Qed.   

  Lemma is_gc_access l E: ↑gcN ⊆ E → gc_inv -∗ is_gc_loc l ={E, E ∖ ↑gcN}=∗ ∃ v, l ↦ v ∗ (l ↦ v ={E ∖ ↑gcN, E}=∗ ⌜True⌝).
  Proof.
    iIntros (HN) "#Hinv Hgc_l".
    iMod (inv_open_timeless _ gcN _ with "Hinv") as "[P Hclose]"=>//.
    iModIntro.
    iDestruct "P" as (gcm) "[H● HsepM]".
    iDestruct (is_gc_lookup_Some with "Hgc_l H●") as %Hsome.
    destruct Hsome as [v Hsome].
    iDestruct (big_sepM_lookup_acc with "HsepM") as "[Hl HsepM]"=>//. 
    iExists _. iFrame.
    iIntros "Hl".
    iMod ("Hclose" with "[H● HsepM Hl]"); last done.
    iExists _. iFrame.
    by (iApply ("HsepM" with "Hl")).
  Qed.

End gc.
