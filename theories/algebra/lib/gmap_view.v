From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import view updates dfrac.
From iris.algebra Require Export gmap dfrac.
From iris.algebra Require Import local_updates proofmode_classes.
From iris.base_logic Require Import base_logic.
From iris Require Import options.

(** * CMRA for a "view of a gmap".

The authoritative element [gmap_view_auth] is any [gmap K V].  The fragments
[gmap_view_frag] represent ownership of a single key in that map.  Ownership is
governed by a discardable fraction, which provides the possibiltiy to obtain
persistent read-only ownership of a key.

The key frame-preserving updates are [gmap_view_alloc] to allocate a new key,
[gmap_view_update] to update a key given full ownership of the corresponding
fragment, and [gmap_view_freeze] to make a key read-only by discarding any
fraction of the corresponding fragment. Crucially, the latter does not require
owning the authoritative element.

NOTE: The API surface for [gmap_view] is experimental and subject to change.  We
plan to add notations for authoritative elements and fragments, and hope to
support arbitrary maps as fragments. *)

Local Definition gmap_view_fragUR (K : Type) `{Countable K} (V : ofeT) : ucmraT :=
  gmapUR K (prodR dfracR (agreeR V)).

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} (V : ofeT).
  Implicit Types (m : gmap K V) (k : K) (v : V) (n : nat) (f : gmap_view_fragUR K V).

  Local Definition gmap_view_rel_raw n m f : Prop :=
    map_Forall (λ k dv, ∃ v, dv.2 ≡{n}≡ to_agree v ∧ ✓ dv.1 ∧ m !! k = Some v) f.

  Local Lemma gmap_view_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    gmap_view_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    gmap_view_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k [q va] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & [q' va'] & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (v & Hagree & Hdval & Hm1). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as (v' & Hm2 & Hv).
    exists v'. rewrite assoc. split; last done.
    rewrite -Hv.
    destruct Hincl as [[Heqq Heqva]|[Hinclq Hinclva]%pair_includedN].
    - simpl in *. split.
      + rewrite Heqva. eapply dist_le; last eassumption. done.
      + rewrite <-discrete_iff in Heqq; last by apply _.
        fold_leibniz. subst q'. done.
    - split.
      + etrans; last first.
        { eapply dist_le; last eassumption. done. }
        eapply agree_valid_includedN; last done.
        eapply cmra_validN_le; last eassumption.
        rewrite Hagree. done.
      + rewrite <-cmra_discrete_included_iff in Hinclq.
        eapply cmra_valid_included; done.
  Qed.

  Local Lemma gmap_view_rel_raw_valid n m f :
    gmap_view_rel_raw n m f → ✓{n} f.
  Proof.
    intros Hrel k. destruct (f !! k) as [[q va]|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (v & Hagree & Hdval & Hm1). simpl in *.
    split; simpl.
    - apply cmra_discrete_valid_iff. done.
    - rewrite Hagree. done.
  Qed.

  Local Canonical Structure gmap_view_rel : view_rel (gmapO K V) (gmap_view_fragUR K V) :=
    ViewRel gmap_view_rel_raw gmap_view_rel_raw_mono gmap_view_rel_raw_valid.

  Local Lemma gmap_view_rel_discrete :
    OfeDiscrete V → ViewRelDiscrete gmap_view_rel.
  Proof.
    intros ? n m f Hrel k [df va] Hk.
    destruct (Hrel _ _ Hk) as (v & Hagree & Hdval & Hm).
    exists v. split; last by auto.
    eapply discrete_iff; first by apply _.
    eapply discrete_iff; first by apply _.
    done.
  Qed.
End rel.

Local Existing Instance gmap_view_rel_discrete.

Definition gmap_viewUR (K : Type) `{Countable K} (V : ofeT) : ucmraT :=
  viewUR (gmap_view_rel K V).
Definition gmap_viewR (K : Type) `{Countable K} (V : ofeT) : cmraT :=
  viewR (gmap_view_rel K V).
Definition gmap_viewO (K : Type) `{Countable K} (V : ofeT) : ofeT :=
  viewO (gmap_view_rel K V).

Section definitions.
  Context {K : Type} `{Countable K} {V : ofeT}.

  Definition gmap_view_auth (m : gmap K V) : gmap_viewR K V :=
    ●V m.
  Definition gmap_view_frag (k : K) (dq : dfrac) (v : V) : gmap_viewR K V :=
    ◯V {[k := (dq, to_agree v)]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : ofeT}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).

  Global Instance : Params (@gmap_view_auth) 4 := {}.
  Global Instance gmap_view_auth_ne : NonExpansive (gmap_view_auth (K:=K) (V:=V)).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_auth_proper : Proper ((≡) ==> (≡)) (gmap_view_auth (K:=K) (V:=V)).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@gmap_view_frag) 6 := {}.
  Global Instance gmap_view_frag_ne k oq : NonExpansive (gmap_view_frag (V:=V) k oq).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_frag_proper k oq : Proper ((≡) ==> (≡)) (gmap_view_frag (V:=V) k oq).
  Proof. apply ne_proper, _. Qed.

  (* Helper lemmas *)
  Local Lemma gmap_view_rel_lookup n m k dq v :
    gmap_view_rel K V n m {[k := (dq, to_agree v)]} ↔ ✓ dq ∧ m !! k ≡{n}≡ Some v.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (v' & Hagree & Hval & ->).
      { rewrite lookup_singleton. done. }
      simpl in *. apply (inj _) in Hagree. rewrite Hagree.
      done.
    - intros [Hval (v' & Hm & Hv')%dist_Some_inv_r'] j [df va].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v'. split_and!; by rewrite ?Hv'.
  Qed.

  (** Composition and validity *)
  Lemma gmap_view_auth_valid m : ✓ gmap_view_auth m.
  Proof.
    apply view_auth_valid. intros n l ? Hl. rewrite lookup_empty in Hl. done.
  Qed.

  Lemma gmap_view_frag_validN n k dq v : ✓{n} gmap_view_frag k dq v ↔ ✓ dq.
  Proof.
    rewrite view_frag_validN singleton_validN. split.
    - intros [??]. done.
    - intros ?. split; done.
  Qed.
  Lemma gmap_view_frag_valid k dq v : ✓ gmap_view_frag k dq v ↔ ✓ dq.
  Proof.
    rewrite view_frag_valid singleton_valid. split.
    - intros [??]. done.
    - intros ?. split; done.
  Qed.

  Lemma gmap_view_frag_op k dq1 dq2 v :
    gmap_view_frag k (dq1 ⋅ dq2) v ≡ gmap_view_frag k dq1 v ⋅ gmap_view_frag k dq2 v.
  Proof. rewrite -view_frag_op singleton_op -pair_op agree_idemp //. Qed.
  Lemma gmap_view_frag_add k q1 q2 v :
    gmap_view_frag k (DfracOwn (q1 + q2)) v ≡
      gmap_view_frag k (DfracOwn q1) v ⋅ gmap_view_frag k (DfracOwn q2) v.
  Proof. rewrite -gmap_view_frag_op. done. Qed.

  Lemma gmap_view_frag_op_validN n k dq1 dq2 v1 v2 :
    ✓{n} (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN singleton_op singleton_validN -pair_op.
    split; intros [Hfrac Hagree]; (split; first done); simpl in *.
    - apply to_agree_op_invN. done.
    - rewrite Hagree agree_idemp. done.
  Qed.
  Lemma gmap_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite view_frag_valid singleton_op singleton_valid -pair_op.
    split; intros [Hfrac Hagree]; (split; first done); simpl in *.
    - apply to_agree_op_inv. done.
    - rewrite Hagree agree_idemp. done.
  Qed.
  Lemma gmap_view_frag_op_valid_L `{!LeibnizEquiv V} k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 = v2.
  Proof. unfold_leibniz. apply gmap_view_frag_op_valid. Qed.

  Lemma gmap_view_both_validN n m k dq v :
    ✓{n} (gmap_view_auth m ⋅ gmap_view_frag k dq v) ↔
      ✓ dq ∧ m !! k ≡{n}≡ Some v.
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag.
    rewrite view_both_validN.
    apply gmap_view_rel_lookup.
  Qed.
  Lemma gmap_view_both_valid m k dq v :
    ✓ (gmap_view_auth m ⋅ gmap_view_frag k dq v) ↔
    ✓ dq ∧ m !! k ≡ Some v.
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag.
    rewrite view_both_valid. setoid_rewrite gmap_view_rel_lookup.
    split; intros Hm; split.
    - apply (Hm 0%nat).
    - apply equiv_dist=>n. apply Hm.
    - apply Hm.
    - revert n. apply equiv_dist. apply Hm.
  Qed.
  Lemma gmap_view_both_valid_L `{!LeibnizEquiv V} m k dq v :
    ✓ (gmap_view_auth m ⋅ gmap_view_frag k dq v) ↔
    ✓ dq ∧ m !! k = Some v.
  Proof. unfold_leibniz. apply gmap_view_both_valid. Qed.

  (** Frame-preserving updates *)
  Lemma gmap_view_alloc m k dq v :
    m !! k = None →
    ✓ dq →
    gmap_view_auth m ~~> gmap_view_auth (<[k := v]> m) ⋅ gmap_view_frag k dq v.
  Proof.
    intros Hfresh Hdq. apply view_update_alloc=>n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & _ & _ & Hm).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <- <-]. eexists. do 2 (split; first done).
      rewrite lookup_insert. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & ? & Hm).
      eexists. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma gmap_view_delete m k v :
    gmap_view_auth m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
    gmap_view_auth (delete k m).
  Proof.
    apply view_update_dealloc=>n bf Hrel j [df va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (v' & _ & Hdf & _).
      { rewrite lookup_op Hbf lookup_singleton -Some_op. done. }
      exfalso. apply: dfrac_full_exclusive. apply Hdf.
    - edestruct (Hrel j) as (v' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      exists v'. do 2 (split; first done).
      rewrite lookup_delete_ne //.
  Qed.

  Lemma gmap_view_update m k v v' :
    gmap_view_auth m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
      gmap_view_auth (<[k := v']> m) ⋅ gmap_view_frag k (DfracOwn 1) v'.
  Proof.
    apply view_update=>n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { move: Hrel =>/view_rel_validN /(_ k).
        rewrite lookup_op lookup_singleton.
        destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        rewrite Hbf. clear Hbf.
        rewrite -Some_op -pair_op.
        move=>[/= /dfrac_full_exclusive Hdf _]. done. }
      rewrite Hbf right_id lookup_singleton. clear Hbf.
      intros [= <- <-].
      eexists. do 2 (split; first done).
      rewrite lookup_insert. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      edestruct (Hrel j) as (v'' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // left_id. done. }
      simpl in *. eexists. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma gmap_view_persist k q v :
    gmap_view_frag k (DfracOwn q) v ~~> gmap_view_frag k DfracDiscarded v.
  Proof.
    apply view_update_frag; last first.
    { eapply singleton_update, prod_update; simpl; last done.
      apply dfrac_discard_update. }
    move=>m n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - rewrite lookup_singleton.
      edestruct (Hrel k ((DfracOwn q, to_agree v) ⋅? bf !! k)) as (v' & Hdf & Hva & Hm).
      { rewrite lookup_op lookup_singleton.
        destruct (bf !! k) eqn:Hbf; by rewrite Hbf. }
      rewrite Some_op_opM. intros [= Hbf].
      exists v'. rewrite assoc; split; last done.
      destruct (bf !! k) as [[df' va']|] eqn:Hbfk; rewrite Hbfk in Hbf; clear Hbfk.
      + simpl in *. rewrite -pair_op in Hbf.
        move:Hbf=>[= <- <-]. split; first done.
        eapply cmra_discrete_valid.
        eapply (dfrac_discard_update _ _ (Some df')).
        apply cmra_discrete_valid_iff. done.
      + simpl in *. move:Hbf=>[= <- <-]. split; done.
    - rewrite lookup_singleton_ne //.
      rewrite left_id=>Hbf.
      edestruct (Hrel j) as (v'' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // left_id. done. }
      simpl in *. eexists. do 2 (split; first done). done.
  Qed.

  (** Typeclass instances *)
  Global Instance gmap_view_frag_core_id k dq v : CoreId dq → CoreId (gmap_view_frag k dq v).
  Proof. apply _. Qed.

  Global Instance gmap_view_cmra_discrete : OfeDiscrete V → CmraDiscrete (gmap_viewR K V).
  Proof. apply _. Qed.

  Global Instance gmap_view_frag_mut_is_op dq dq1 dq2 k v :
    IsOp dq dq1 dq2 →
    IsOp' (gmap_view_frag k dq v) (gmap_view_frag k dq1 v) (gmap_view_frag k dq2 v).
  Proof. rewrite /IsOp' /IsOp => ->. apply gmap_view_frag_op. Qed.

  (** Internalized properties *)
  Lemma gmap_view_both_validI M m k dq v :
    ✓ (gmap_view_auth m ⋅ gmap_view_frag k dq v) ⊢@{uPredI M}
    ✓ dq ∧ m !! k ≡ Some v.
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag. apply view_both_validI_1.
    intros n a. uPred.unseal. apply gmap_view_rel_lookup.
  Qed.

  Lemma gmap_view_frag_op_validI M k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ⊢@{uPredI M}
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite /gmap_view_frag -view_frag_op view_frag_validI.
    rewrite singleton_op singleton_validI -pair_op uPred.prod_validI /=.
    apply bi.and_mono; first done.
    rewrite agree_validI agree_equivI. done.
  Qed.

End lemmas.

(** Functor *)
Program Definition gmap_viewURF (K : Type) `{Countable K} (F : oFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := gmap_viewUR K (oFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_rel K (oFunctor_car F A1 B1))
              (rel':=gmap_view_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, oFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_ne. done.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -{2}(agree_map_id va).
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -agree_map_compose.
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_compose.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply: view_map_cmra_morphism; [apply _..|]=> n m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel. destruct Hrel as (v & Hagree & Hdval & Hm).
  exists (oFunctor_map F fg v).
  rewrite Hm. split; last by auto.
  rewrite Hagree. rewrite agree_map_to_agree. done.
Qed.

Instance gmap_viewURF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → urFunctorContractive (gmap_viewURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply oFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_contractive. done.
Qed.

Program Definition gmap_viewRF (K : Type) `{Countable K} (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := gmap_viewR K (oFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_rel K (oFunctor_car F A1 B1))
              (rel':=gmap_view_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Solve Obligations with apply gmap_viewURF.

Instance gmap_viewRF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → rFunctorContractive (gmap_viewRF K F).
Proof. apply gmap_viewURF_contractive. Qed.

Typeclasses Opaque gmap_view_auth gmap_view_frag.
