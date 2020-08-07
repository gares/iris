From iris.proofmode Require Import tactics.
From iris.algebra Require Export auth gmap updates csum.
From iris.algebra Require Import local_updates proofmode_classes.
From iris.base_logic Require Import base_logic.
From iris Require Import options.

(** * Authoritative CMRA over a map.
The elements of the map are of type [(frac * agree T) + agree T].
"Right" elements (on the [agree] side) are immutable and their (fragment) ownership is persistent.
"Left" elements behave like the usual separation logic heap with fractional permissions.

This representation and the types of [gmap_auth_auth] and [gmap_auth_frag] are
considered unstable and will change in a future version of Iris. However,
the [mut]/[ro] variants should be unaffected by that change. *)

Local Definition mapUR (K : Type) `{Countable K} (V : ofeT) : ucmraT :=
  gmapUR K (csumR (prodR fracR (agreeR V)) (agreeR V)).
Definition gmap_authR (K : Type) `{Countable K} (V : ofeT) : cmraT :=
  authR (mapUR K V).
Definition gmap_authUR (K : Type) `{Countable K} (V : ofeT) : ucmraT :=
  authUR (mapUR K V).

(** The abstract state of the authoritative map is given by a [gmap K (V*bool)],
where the [bool] indicates if the element is still mutable ([false] = "left
element") or already read-only ([true] = "right element"). *)

Section definitions.
  Context {K : Type} `{Countable K} {V : ofeT}.

  Local Definition to_auth_elem (q : frac) (e : bool * V) :
      csumR (prodR fracR (agreeR V)) (agreeR V) :=
    if e.1 then Cinr (to_agree e.2) else Cinl (q, to_agree e.2).
  Local Definition to_auth_map (m : gmap K (bool * V)) : mapUR K V :=
    to_auth_elem 1 <$> m.
  Local Definition to_frag_elem (mq : option Qp) (v : V) :
      csumR (prodR fracR (agreeR V)) (agreeR V) :=
    match mq with
    | Some q => Cinl (q, to_agree v)
    | None => Cinr (to_agree v)
    end.

  Definition gmap_auth_auth (m : gmap K (bool * V)) : gmap_authUR K V :=
    ● (to_auth_map m).
  (* [(false,.)] is [λ v, (false, v)]. *)
  Definition gmap_auth_auth_mut (m : gmap K V) : gmap_authUR K V :=
    gmap_auth_auth ((false,.) <$> m).
  Definition gmap_auth_auth_ro (m : gmap K V) : gmap_authUR K V :=
    gmap_auth_auth ((true,.) <$> m).

  Definition gmap_auth_frag (k : K) (mq : option Qp) (v : V) : gmap_authUR K V :=
    ◯ {[k := to_frag_elem mq v]}.
  Definition gmap_auth_frag_mut (k : K) (q : Qp) (v : V) : gmap_authUR K V :=
    gmap_auth_frag k (Some q) v.
  Definition gmap_auth_frag_ro (k : K) (v : V) : gmap_authUR K V :=
    gmap_auth_frag k None v.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : ofeT}.
  Implicit Types (m : gmap K (bool * V)) (k : K) (q : Qp) (v : V) (ro : bool) (e : bool * V).

  Local Instance to_auth_elem_ne q : NonExpansive (to_auth_elem (V:=V) q).
  Proof. intros n [v1 ro1] [v2 ro2] [??]. simpl in *. solve_proper. Qed.
  Global Instance gmap_auth_auth_ne : NonExpansive (gmap_auth_auth (K:=K) (V:=V)).
  Proof. solve_proper. Qed.
  Global Instance gmap_auth_auth_mut_ne : NonExpansive (gmap_auth_auth_mut (K:=K) (V:=V)).
  Proof. solve_proper. Qed.
  Global Instance gmap_auth_auth_ro_ne : NonExpansive (gmap_auth_auth_ro (K:=K) (V:=V)).
  Proof. solve_proper. Qed.

  Local Instance to_frag_elem_ne oq : NonExpansive (to_frag_elem (V:=V) oq).
  Proof. solve_proper. Qed.
  Global Instance gmap_auth_frag_ne k oq : NonExpansive (gmap_auth_frag (V:=V) k oq).
  Proof. solve_proper. Qed.
  Global Instance gmap_auth_frag_mut_ne k q : NonExpansive (gmap_auth_frag_mut (V:=V) k q).
  Proof. solve_proper. Qed.
  Global Instance gmap_auth_frag_ro_ne k : NonExpansive (gmap_auth_frag_ro (V:=V) k).
  Proof. solve_proper. Qed.

  (** Map operations *)
  Local Lemma to_auth_map_insert k e m :
    to_auth_map (<[k:=e]> m) = <[k:=to_auth_elem 1 e]> (to_auth_map m).
  Proof. by rewrite /to_auth_map fmap_insert. Qed.
  Local Lemma to_auth_map_singleton_includedN qe n m k e :
    {[k := to_auth_elem qe e]} ≼{n} to_auth_map m → m !! k ≡{n}≡ Some e.
  Proof.
    rewrite singleton_includedN_l => -[auth_e []].
    rewrite /to_auth_map lookup_fmap fmap_Some_dist => -[e' [-> ->]] {m}.
    rewrite Some_csum_includedN. intros [Hbot|[Hleft|Hright]].
    - exfalso. destruct e' as [[] ?]; done.
    - destruct Hleft as ([q v] & [q' v'] & He & He' & Hincl).
      destruct e as [[] ev]; first done.
      destruct e' as [[] ev']; first done.
      f_equiv. f_equiv.
      rewrite /to_auth_elem /= in He He'.
      move:He He'=> [_ Heq] [_ Heq']. simplify_eq.
      move:Hincl=> /Some_pair_includedN_total_2 [_] /to_agree_includedN. done.
    - destruct Hright as (v & v' & He & He' & Hincl).
      destruct e as [[] ev]; last done.
      destruct e' as [[] ev']; last done.
      f_equiv. f_equiv.
      rewrite /to_auth_elem /= in He He'.
      move:He He'=> [Heq] [Heq']. simplify_eq.
      move:Hincl=> /Some_includedN [|].
      * move /to_agree_injN. done.
      * move /to_agree_includedN. done.
  Qed.
  Local Lemma to_auth_map_singleton_included qe m k e :
    (∀ n, {[k := to_auth_elem qe e]} ≼{n} to_auth_map m) → m !! k ≡ Some e.
  Proof.
    intros Hincl. apply equiv_dist=>n.
    by eapply to_auth_map_singleton_includedN.
  Qed.
  Local Lemma to_auth_map_singleton_includedI qe M m c k e :
    to_auth_map m ≡ {[k := to_auth_elem qe e]} ⋅ c ⊢@{uPredI M} m !! k ≡ Some e.
  Proof.
    apply uPred.internal_eq_entails=>n Heq.
    eapply to_auth_map_singleton_includedN.
    by exists c.
  Qed.

  (** Composition and validity *)
  Local Lemma to_auth_elem_valid e : ✓ to_auth_elem 1 e.
  Proof. destruct e as [ro v]. by destruct ro. Qed.

  Lemma gmap_auth_auth_valid m : ✓ gmap_auth_auth m.
  Proof.
    rewrite auth_auth_valid. intros l. rewrite lookup_fmap. case (m !! l); last done.
    apply to_auth_elem_valid.
  Qed.
  Lemma gmap_auth_auth_mut_valid (m : gmap K V) : ✓ gmap_auth_auth_mut m.
  Proof. apply gmap_auth_auth_valid. Qed.
  Lemma gmap_auth_auth_ro_valid (m : gmap K V) : ✓ gmap_auth_auth_ro m.
  Proof. apply gmap_auth_auth_valid. Qed.

  Lemma gmap_auth_frag_valid k mq v : ✓ gmap_auth_frag k mq v ↔ ✓ mq.
  Proof.
    rewrite auth_frag_valid singleton_valid. split.
    - destruct mq; last done. intros [??]. done.
    - intros ?. destruct mq; split; done.
  Qed.
  Lemma gmap_auth_frag_mut_valid k q v : ✓ gmap_auth_frag_mut k q v ↔ ✓ q.
  Proof. apply gmap_auth_frag_valid. Qed.
  Lemma gmap_auth_frag_ro_valid k v : ✓ gmap_auth_frag_ro k v.
  Proof. apply gmap_auth_frag_valid. done. Qed.

  Lemma gmap_auth_frag_mut_frac_op k q1 q2 v :
    gmap_auth_frag_mut k (q1 + q2)%Qp v ≡ gmap_auth_frag_mut k q1 v ⋅ gmap_auth_frag_mut k q2 v.
  Proof. rewrite -auth_frag_op singleton_op -Cinl_op -pair_op agree_idemp //. Qed.
  Lemma gmap_auth_frag_mut_op_valid k q1 q2 v1 v2 :
    ✓ (gmap_auth_frag_mut k q1 v1 ⋅ gmap_auth_frag_mut k q2 v2) → ✓ (q1 + q2)%Qp ∧ v1 ≡ v2.
  Proof.
    rewrite auth_frag_valid singleton_op singleton_valid -Cinl_op -pair_op.
    intros [? ?]. split; first done. apply to_agree_op_inv. done.
  Qed.
  Lemma gmap_auth_frag_mut_op_valid_L `{!LeibnizEquiv V} k q1 q2 v1 v2 :
    ✓ (gmap_auth_frag_mut k q1 v1 ⋅ gmap_auth_frag_mut k q2 v2) → ✓ (q1 + q2)%Qp ∧ v1 = v2.
  Proof.
    unfold_leibniz. apply gmap_auth_frag_mut_op_valid.
  Qed.

  Lemma gmap_auth_frag_ro_op_mut_op_valid k q1 v1 v2 :
    ¬ ✓ (gmap_auth_frag_mut k q1 v1 ⋅ gmap_auth_frag_ro k v2).
  Proof. rewrite auth_frag_valid singleton_op singleton_valid. intros []. Qed.

  Lemma gmap_auth_frag_ro_idemp k v :
    gmap_auth_frag_ro k v ≡ gmap_auth_frag_ro k v ⋅ gmap_auth_frag_ro k v.
  Proof. rewrite -auth_frag_op singleton_op -Cinr_op agree_idemp. done. Qed.

  Lemma gmap_auth_frag_ro_op_valid k v1 v2 :
    ✓ (gmap_auth_frag_ro k v1 ⋅ gmap_auth_frag_ro k v2) → v1 ≡ v2.
  Proof.
    rewrite auth_frag_valid singleton_op singleton_valid -Cinr_op.
    apply to_agree_op_inv.
  Qed.
  Lemma gmap_auth_frag_ro_op_valid_L `{!LeibnizEquiv V} k v1 v2 :
    ✓ (gmap_auth_frag_ro k v1 ⋅ gmap_auth_frag_ro k v2) → v1 = v2.
  Proof.
    unfold_leibniz. apply gmap_auth_frag_ro_op_valid.
  Qed.

  Lemma gmap_auth_auth_frag_valid m k mq v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag k mq v) →
    m !! k ≡ Some (if mq is None then true else false, v).
  Proof.
    rewrite /gmap_auth_auth /gmap_auth_frag.
    intros [Hlk _]%auth_both_valid.
    set (q := default 1%Qp mq).
    eapply (to_auth_map_singleton_included q).
    rewrite /to_auth_elem /to_frag_elem /= in Hlk *.
    destruct mq; done.
  Qed.

  Lemma gmap_auth_auth_frag_mut_valid m k q v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag_mut k q v) → m !! k ≡ Some (false, v).
  Proof. apply gmap_auth_auth_frag_valid. Qed.
  Lemma gmap_auth_auth_frag_mut_valid_L `{!LeibnizEquiv V} m k q v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag_mut k q v) → m !! k = Some (false, v).
  Proof. unfold_leibniz. apply gmap_auth_auth_frag_mut_valid. Qed.
  Lemma gmap_auth_auth_mut_frag_mut_valid (m : gmap K V) k q v :
    ✓ (gmap_auth_auth_mut m ⋅ gmap_auth_frag_mut k q v) → m !! k ≡ Some v.
  Proof.
    rewrite /gmap_auth_auth_mut. move /gmap_auth_auth_frag_mut_valid.
    rewrite lookup_fmap /= fmap_Some_equiv => -[e [-> [/= _ ?]]]. by f_equiv.
  Qed.
  Lemma gmap_auth_auth_mut_frag_mut_valid_L `{!LeibnizEquiv V} (m : gmap K V) k q v :
    ✓ (gmap_auth_auth_mut m ⋅ gmap_auth_frag_mut k q v) → m !! k = Some v.
  Proof. unfold_leibniz. apply gmap_auth_auth_mut_frag_mut_valid. Qed.

  Lemma gmap_auth_auth_frag_ro_valid m k v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag_ro k v) → m !! k ≡ Some (true, v).
  Proof. apply gmap_auth_auth_frag_valid. Qed.
  Lemma gmap_auth_auth_frag_ro_valid_L `{!LeibnizEquiv V} m k v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag_ro k v) → m !! k = Some (true, v).
  Proof. unfold_leibniz. apply gmap_auth_auth_frag_ro_valid. Qed.
  Lemma gmap_auth_auth_ro_frag_ro_valid (m : gmap K V) k v :
    ✓ (gmap_auth_auth_ro m ⋅ gmap_auth_frag_ro k v) → m !! k ≡ Some v.
  Proof.
    rewrite /gmap_auth_auth_mut. move /gmap_auth_auth_frag_ro_valid.
    rewrite lookup_fmap /= fmap_Some_equiv => -[e [-> [/= _ ?]]]. by f_equiv.
  Qed.
  Lemma gmap_auth_auth_ro_frag_ro_valid_L `{!LeibnizEquiv V} (m : gmap K V) k v :
    ✓ (gmap_auth_auth_ro m ⋅ gmap_auth_frag_ro k v) → m !! k = Some v.
  Proof. unfold_leibniz. apply gmap_auth_auth_ro_frag_ro_valid. Qed.

  (** Frame-preserving updates *)
  Lemma gmap_auth_alloc m k v ro :
    m !! k = None →
    gmap_auth_auth m ~~>
      gmap_auth_auth (<[k := (ro, v)]> m) ⋅
        gmap_auth_frag k (if ro then None else Some 1%Qp) v.
  Proof.
    intros Hfresh. etrans.
    - eapply auth_update_alloc.
      eapply (alloc_singleton_local_update _ k (to_auth_elem _ (ro, v)))=> //.
      + rewrite lookup_fmap Hfresh. done.
      + apply to_auth_elem_valid.
    - apply reflexive_eq. f_equal.
      + rewrite /gmap_auth_auth to_auth_map_insert. done.
      + destruct ro; done.
  Qed.
  Lemma gmap_auth_mut_alloc (m : gmap K V) k v :
    m !! k = None →
    gmap_auth_auth_mut m ~~>
      gmap_auth_auth_mut (<[k := v]> m) ⋅ gmap_auth_frag_mut k 1%Qp v.
  Proof.
    intros Hfresh.
    etrans; first apply (gmap_auth_alloc _ k v false).
    - rewrite lookup_fmap Hfresh //.
    - apply reflexive_eq. f_equal. rewrite /gmap_auth_auth_mut fmap_insert //.
  Qed.
  Lemma gmap_auth_ro_alloc (m : gmap K V) k v :
    m !! k = None →
    gmap_auth_auth_ro m ~~> gmap_auth_auth_ro (<[k := v]> m) ⋅ gmap_auth_frag_ro k v.
  Proof.
    intros Hfresh.
    etrans; first apply (gmap_auth_alloc _ k v true).
    - rewrite lookup_fmap Hfresh //.
    - apply reflexive_eq. f_equal. rewrite /gmap_auth_auth_ro fmap_insert //.
  Qed.

  Lemma gmap_auth_update m k v v' ro :
    gmap_auth_auth m ⋅ gmap_auth_frag_mut k 1%Qp v ~~>
      gmap_auth_auth (<[k := (ro, v')]> m) ⋅
        gmap_auth_frag k (if ro then None else Some 1%Qp) v'.
  Proof.
    etrans.
    - apply cmra_update_valid0=>Hval.
      eapply auth_update, singleton_local_update_any=>??.
      eapply (exclusive_local_update _ (to_auth_elem _ (ro, v'))).
      apply to_auth_elem_valid.
    - apply reflexive_eq. f_equal.
      + rewrite /gmap_auth_auth to_auth_map_insert. done.
      + destruct ro; done.
  Qed.
  Lemma gmap_auth_freeze m k v :
    gmap_auth_auth m ⋅ gmap_auth_frag_mut k 1%Qp v ~~>
      gmap_auth_auth (<[k := (true, v)]> m) ⋅ gmap_auth_frag_ro k v.
  Proof.
    etrans; first apply gmap_auth_update with (ro:=true).
    apply reflexive_eq. f_equal.
  Qed.
  Lemma gmap_auth_mut_update (m : gmap K V) k v v' :
    gmap_auth_auth_mut m ⋅ gmap_auth_frag_mut k 1%Qp v ~~>
      gmap_auth_auth_mut (<[k := v']> m) ⋅ gmap_auth_frag_mut k 1%Qp v'.
  Proof.
    etrans; first apply gmap_auth_update with (ro:=false).
    apply reflexive_eq. rewrite /gmap_auth_auth_mut fmap_insert.
    f_equal.
  Qed.

  (** Typeclass instances
  (These overlap up to conversion, but the functions are made TC-opaque below.) *)
  Global Instance gmap_auth_frag_core_id k v :
    CoreId (gmap_auth_frag k None v).
  Proof. apply _. Qed.
  Global Instance gmap_auth_frag_ro_core_id k v :
    CoreId (gmap_auth_frag_ro k v).
  Proof. apply _. Qed.

  Global Instance gmap_auth_frag_mut_is_op q q1 q2 k v :
    IsOp q q1 q2 →
    IsOp' (gmap_auth_frag_mut k q v) (gmap_auth_frag_mut k q1 v) (gmap_auth_frag_mut k q2 v).
  Proof. rewrite /IsOp' /IsOp => ->. apply gmap_auth_frag_mut_frac_op. Qed.

  (** Internalized properties *)
  Lemma gmap_auth_auth_frag_validI M m k mq v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag k mq v) ⊢@{uPredI M}
    m !! k ≡ Some (if mq is None then true else false, v).
  Proof.
    rewrite /gmap_auth_auth /gmap_auth_frag_mut.
    rewrite auth_both_validI. iIntros "[Hmap Hval]".
    iDestruct "Hmap" as (c) "Hmap".
    set (q := default 1%Qp mq).
    iApply (to_auth_map_singleton_includedI q).
    destruct mq; try done.
  Qed.

  Lemma gmap_auth_auth_frag_mut_validI M m k q v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag_mut k q v) ⊢@{uPredI M} m !! k ≡ Some (false, v).
  Proof. apply gmap_auth_auth_frag_validI. Qed.
  Lemma gmap_auth_auth_ro_frag_mut_validI M (m : gmap K V) k q v :
    ✓ (gmap_auth_auth_mut m ⋅ gmap_auth_frag_mut k q v) ⊢@{uPredI M} m !! k ≡ Some v.
  Proof.
    rewrite /gmap_auth_auth_mut gmap_auth_auth_frag_mut_validI lookup_fmap /=.
    rewrite !option_equivI. destruct (m !! k); simpl; last done.
    rewrite prod_equivI /=. iIntros "[_ Heq]". done.
  Qed.
  Lemma gmap_auth_auth_frag_ro_validI M m k v :
    ✓ (gmap_auth_auth m ⋅ gmap_auth_frag_ro k v) ⊢@{uPredI M} m !! k ≡ Some (true, v).
  Proof. apply gmap_auth_auth_frag_validI. Qed.
  Lemma gmap_auth_auth_ro_frag_ro_validI M (m : gmap K V) k v :
    ✓ (gmap_auth_auth_ro m ⋅ gmap_auth_frag_ro k v) ⊢@{uPredI M} m !! k ≡ Some v.
  Proof.
    rewrite /gmap_auth_auth_ro gmap_auth_auth_frag_ro_validI lookup_fmap /=.
    rewrite !option_equivI. destruct (m !! k); simpl; last done.
    rewrite prod_equivI /=. iIntros "[_ Heq]". done.
  Qed.

End lemmas.

(** Functor *)
Definition gmap_authRF (K : Type) `{Countable K} (F : oFunctor) : rFunctor :=
  authRF (gmapURF K (csumRF (prodRF fracR (agreeRF F)) (agreeRF F))).
Instance gmap_authRF_contractive {K : Type} `{Countable K} (F : oFunctor) :
  oFunctorContractive F → rFunctorContractive (gmap_authRF K F).
Proof. apply _. Qed.

Definition gmap_authURF (K : Type) `{Countable K} (F : oFunctor) : urFunctor :=
  authURF (gmapURF K (csumRF (prodRF fracR (agreeRF F)) (agreeRF F))).
Instance gmap_authURF_contractive {K : Type} `{Countable K} (F : oFunctor) :
  oFunctorContractive F → urFunctorContractive (gmap_authURF K F).
Proof. apply _. Qed.

Typeclasses Opaque gmap_auth_auth gmap_auth_auth_mut gmap_auth_auth_ro
  gmap_auth_frag gmap_auth_frag_mut gmap_auth_frag_ro gmap_authRF gmap_authURF.
