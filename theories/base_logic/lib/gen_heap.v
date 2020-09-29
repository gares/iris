From stdpp Require Export namespaces.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap frac agree namespace_map.
From iris.base_logic.lib Require Export own.
From iris Require Import options.
Import uPred.

(** This file provides a generic mechanism for a point-to connective [l ↦{q} v]
with fractional permissions (where [l : L] and [v : V] over some abstract type
[L] for locations and [V] for values). This mechanism can be plugged into a
language by using the heap invariant [gen_heap_ctx σ] where [σ : gmap L V]. See
heap-lang for an example.

Next to the point-to connective [l ↦{q} v], which keeps track of the value [v]
of a location [l], this mechanism allows one to attach "meta" or "ghost" data to
locations. This is done as follows:

- When one allocates a location, in addition to the point-to connective [l ↦ v],
  one also obtains the token [meta_token l ⊤]. This token is an exclusive
  resource that denotes that no meta data has been associated with the
  namespaces in the mask [⊤] for the location [l].
- Meta data tokens can be split w.r.t. namespace masks, i.e.
  [meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2] if [E1 ## E2].
- Meta data can be set using the update [meta_token l E ==∗ meta l N x] provided
  [↑N ⊆ E], and [x : A] for any countable [A]. The [meta l N x] connective is
  persistent and denotes the knowledge that the meta data [x] has been
  associated with namespace [N] to the location [l].

To make the mechanism as flexible as possible, the [x : A] in [meta l N x] can
be of any countable type [A]. This means that you can associate e.g. single
ghost names, but also tuples of ghost names, etc.

To further increase flexibility, the [meta l N x] and [meta_token l E]
connectives are annotated with a namespace [N] and mask [E]. That way, one can
assign a map of meta information to a location. This is particularly useful when
building abstractions, then one can gradually assign more ghost information to a
location instead of having to do all of this at once. We use namespaces so that
these can be matched up with the invariant namespaces. *)

(** To implement this mechanism, we use three resource algebras:

- An authoritative RA over [gmap L (fracR * agreeR V)], which keeps track of the
  values of locations.
- An authoritative RA over [gmap L (agree gname)], which keeps track of the meta
  information of locations. This RA introduces an indirection, it keeps track of
  a ghost name for each location.
- The ghost names in the aforementioned authoritative RA refer to namespace maps
  [namespace_map (agree positive)], which store the actual meta information.
  This indirection is needed because we cannot perform frame preserving updates
  in an authoritative fragment without owning the full authoritative element
  (in other words, without the indirection [meta_set] would need [gen_heap_ctx]
  as a premise).

Note that in principle we could have used one big authoritative RA to keep track
of both values and ghost names for meta information, for example:
[gmap L (option (fracR * agreeR V) ∗ option (agree gname)]. Due to the [option]s,
this RA would be quite inconvenient to deal with. *)

Definition gen_heapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR fracR (agreeR (leibnizO V))).
Definition gen_metaUR (L : Type) `{Countable L} : ucmraT :=
  gmapUR L (agreeR gnameO).

Definition to_gen_heap {L V} `{Countable L} : gmap L V → gen_heapUR L V :=
  fmap (λ v, (1%Qp, to_agree (v : leibnizO V))).
Definition to_gen_meta `{Countable L} : gmap L gname → gen_metaUR L :=
  fmap to_agree.

(** The CMRA we need. *)
Class gen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapG {
  gen_heap_inG :> inG Σ (authR (gen_heapUR L V));
  gen_meta_inG :> inG Σ (authR (gen_metaUR L));
  gen_meta_data_inG :> inG Σ (namespace_mapR (agreeR positiveO));
  gen_heap_name : gname;
  gen_meta_name : gname
}.
Arguments gen_heap_name {L V Σ _ _} _ : assert.
Arguments gen_meta_name {L V Σ _ _} _ : assert.

Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_preG_inG :> inG Σ (authR (gen_heapUR L V));
  gen_meta_preG_inG :> inG Σ (authR (gen_metaUR L));
  gen_meta_data_preG_inG :> inG Σ (namespace_mapR (agreeR positiveO));
}.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (authR (gen_heapUR L V));
  GFunctor (authR (gen_metaUR L));
  GFunctor (namespace_mapR (agreeR positiveO))
].

Instance subG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_heapG L V Σ}.

  Definition gen_heap_ctx (σ : gmap L V) : iProp Σ := ∃ m,
    (* The [⊆] is used to avoid assigning ghost information to the locations in
    the initial heap (see [gen_heap_init]). *)
    ⌜ dom _ m ⊆ dom (gset L) σ ⌝ ∧
    own (gen_heap_name hG) (● (to_gen_heap σ)) ∗
    own (gen_meta_name hG) (● (to_gen_meta m)).

  Definition mapsto_def (l : L) (q : Qp) (v: V) : iProp Σ :=
    own (gen_heap_name hG) (◯ {[ l := (q, to_agree (v : leibnizO V)) ]}).
  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).

  Definition meta_token_def (l : L) (E : coPset) : iProp Σ :=
    ∃ γm, own (gen_meta_name hG) (◯ {[ l := to_agree γm ]}) ∗
          own γm (namespace_map_token E).
  Definition meta_token_aux : seal (@meta_token_def). Proof. by eexists. Qed.
  Definition meta_token := meta_token_aux.(unseal).
  Definition meta_token_eq : @meta_token = @meta_token_def := meta_token_aux.(seal_eq).

  Definition meta_def `{Countable A} (l : L) (N : namespace) (x : A) : iProp Σ :=
    ∃ γm, own (gen_meta_name hG) (◯ {[ l := to_agree γm ]}) ∗
          own γm (namespace_map_data N (to_agree (encode x))).
  Definition meta_aux : seal (@meta_def). Proof. by eexists. Qed.
  Definition meta := meta_aux.(unseal).
  Definition meta_eq : @meta = @meta_def := meta_aux.(seal_eq).
End definitions.
Arguments meta {L _ _ V Σ _ A _ _} l N x.

Local Notation "l ↦{ q } v" := (mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l 1 v) (at level 20) : bi_scope.

Local Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Local Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section to_gen_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.

  (** Conversion to heaps and back *)
  Lemma to_gen_heap_valid σ : ✓ to_gen_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma lookup_to_gen_heap_None σ l : σ !! l = None → to_gen_heap σ !! l = None.
  Proof. by rewrite /to_gen_heap lookup_fmap=> ->. Qed.
  Lemma gen_heap_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_gen_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_gen_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.
  Lemma to_gen_heap_insert l v σ :
    to_gen_heap (<[l:=v]> σ) = <[l:=(1%Qp, to_agree (v:leibnizO V))]> (to_gen_heap σ).
  Proof. by rewrite /to_gen_heap fmap_insert. Qed.

  Lemma to_gen_meta_valid m : ✓ to_gen_meta m.
  Proof. intros l. rewrite lookup_fmap. by case (m !! l). Qed.
  Lemma lookup_to_gen_meta_None m l : m !! l = None → to_gen_meta m !! l = None.
  Proof. by rewrite /to_gen_meta lookup_fmap=> ->. Qed.
  Lemma to_gen_meta_insert l m γm :
    to_gen_meta (<[l:=γm]> m) = <[l:=to_agree γm]> (to_gen_meta m).
  Proof. by rewrite /to_gen_meta fmap_insert. Qed.
End to_gen_heap.

Lemma gen_heap_init `{Countable L, !gen_heapPreG L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapG L V Σ, gen_heap_ctx σ.
Proof.
  iMod (own_alloc (● to_gen_heap σ)) as (γh) "Hh".
  { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
  iMod (own_alloc (● to_gen_meta ∅)) as (γm) "Hm".
  { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
  iModIntro. iExists (GenHeapG L V Σ _ _ _ _ _ γh γm).
  iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L.
Qed.

Section gen_heap.
  Context {L V} `{Countable L, !gen_heapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.
  Implicit Types h g : gen_heapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance mapsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q. by rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op
      singleton_op -pair_op agree_idemp.
  Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv. rewrite auth_frag_valid singleton_op singleton_valid -pair_op.
    by intros [_ ?%to_agree_op_inv_L].
  Qed.

  Lemma mapsto_combine l q1 q2 v1 v2 :
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ l ↦{q1 + q2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapsto_agree with "Hl1 Hl2") as %->.
    iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.

  Global Instance ex_mapsto_fractional l : Fractional (λ q, l ↦{q} -)%I.
  Proof.
    intros p q. iSplit.
    - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (mapsto_agree with "H1 H2") as %->. iExists v2. by iFrame.
  Qed.
  Global Instance ex_mapsto_as_fractional l q :
    AsFractional (l ↦{q} -) (λ q, l ↦{q} -)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_valid l q v : l ↦{q} v -∗ ✓ q.
  Proof.
    rewrite mapsto_eq /mapsto_def own_valid !discrete_valid -auth_frag_valid.
    by apply pure_mono=> /singleton_valid [??].
  Qed.
  Lemma mapsto_valid_2 l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %->.
    iApply (mapsto_valid l _ v2). by iFrame.
  Qed.

  Lemma mapsto_mapsto_ne l1 l2 q1 q2 v1 v2 :
    ¬ ✓(q1 + q2)%Qp → l1 ↦{q1} v1 -∗ l2 ↦{q2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof.
    iIntros (?) "Hl1 Hl2"; iIntros (->).
    by iDestruct (mapsto_valid_2 with "Hl1 Hl2") as %?.
  Qed.

  (** General properties of [meta] and [meta_token] *)
  Global Instance meta_token_timeless l N : Timeless (meta_token l N).
  Proof. rewrite meta_token_eq /meta_token_def. apply _. Qed.
  Global Instance meta_timeless `{Countable A} l N (x : A) : Timeless (meta l N x).
  Proof. rewrite meta_eq /meta_def. apply _. Qed.
  Global Instance meta_persistent `{Countable A} l N (x : A) : Persistent (meta l N x).
  Proof. rewrite meta_eq /meta_def. apply _. Qed.

  Lemma meta_token_union_1 l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) -∗ meta_token l E1 ∗ meta_token l E2.
  Proof.
    rewrite meta_token_eq /meta_token_def. intros ?. iDestruct 1 as (γm1) "[#Hγm Hm]".
    rewrite namespace_map_token_union //. iDestruct "Hm" as "[Hm1 Hm2]".
    iSplitL "Hm1"; eauto.
  Qed.
  Lemma meta_token_union_2 l E1 E2 :
    meta_token l E1 -∗ meta_token l E2 -∗ meta_token l (E1 ∪ E2).
  Proof.
    rewrite meta_token_eq /meta_token_def.
    iDestruct 1 as (γm1) "[#Hγm1 Hm1]". iDestruct 1 as (γm2) "[#Hγm2 Hm2]".
    iAssert ⌜ γm1 = γm2 ⌝%I as %->.
    { iDestruct (own_valid_2 with "Hγm1 Hγm2") as %Hγ; iPureIntro.
      move: Hγ. rewrite -auth_frag_op singleton_op=> /auth_frag_valid /=.
      rewrite singleton_valid. apply: to_agree_op_inv_L. }
    iDestruct (own_valid_2 with "Hm1 Hm2") as %?%namespace_map_token_valid_op.
    iExists γm2. iFrame "Hγm2". rewrite namespace_map_token_union //. by iSplitL "Hm1".
  Qed.
  Lemma meta_token_union l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2.
  Proof.
    intros; iSplit; first by iApply meta_token_union_1.
    iIntros "[Hm1 Hm2]". by iApply (meta_token_union_2 with "Hm1 Hm2").
  Qed.

  Lemma meta_token_difference l E1 E2 :
    E1 ⊆ E2 → meta_token l E2 ⊣⊢ meta_token l E1 ∗ meta_token l (E2 ∖ E1).
  Proof.
    intros. rewrite {1}(union_difference_L E1 E2) //.
    by rewrite meta_token_union; last set_solver.
  Qed.

  Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
    meta l i x1 -∗ meta l i x2 -∗ ⌜x1 = x2⌝.
  Proof.
    rewrite meta_eq /meta_def.
    iDestruct 1 as (γm1) "[Hγm1 Hm1]"; iDestruct 1 as (γm2) "[Hγm2 Hm2]".
    iAssert ⌜ γm1 = γm2 ⌝%I as %->.
    { iDestruct (own_valid_2 with "Hγm1 Hγm2") as %Hγ; iPureIntro.
      move: Hγ. rewrite -auth_frag_op singleton_op=> /auth_frag_valid /=.
      rewrite singleton_valid. apply: to_agree_op_inv_L. }
    iDestruct (own_valid_2 with "Hm1 Hm2") as %Hγ; iPureIntro.
    move: Hγ. rewrite -namespace_map_data_op namespace_map_data_valid.
    move=> /to_agree_op_inv_L. naive_solver.
  Qed.
  Lemma meta_set `{Countable A} E l (x : A) N :
    ↑ N ⊆ E → meta_token l E ==∗ meta l N x.
  Proof.
    rewrite meta_token_eq meta_eq /meta_token_def /meta_def.
    iDestruct 1 as (γm) "[Hγm Hm]". iExists γm. iFrame "Hγm".
    iApply (own_update with "Hm"). by apply namespace_map_alloc_update.
  Qed.

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_ctx σ ==∗ gen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v ∗ meta_token l ⊤.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_ctx mapsto_eq /mapsto_def meta_token_eq /meta_token_def /=.
    iDestruct 1 as (m Hσm) "[Hσ Hm]".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (1%Qp, to_agree (v:leibnizO _)))=> //.
      by apply lookup_to_gen_heap_None. }
    iMod (own_alloc (namespace_map_token ⊤)) as (γm) "Hγm".
    { apply namespace_map_token_valid. }
    iMod (own_update with "Hm") as "[Hm Hlm]".
    { eapply auth_update_alloc.
      eapply (alloc_singleton_local_update _ l (to_agree γm))=> //.
      apply lookup_to_gen_meta_None.
      move: Hσl. rewrite -!(not_elem_of_dom (D:=gset L)). set_solver. }
    iModIntro. iFrame "Hl". iSplitL "Hσ Hm"; last by eauto with iFrame.
    iExists (<[l:=γm]> m).
    rewrite to_gen_heap_insert to_gen_meta_insert !dom_insert_L. iFrame.
    iPureIntro. set_solver.
  Qed.

  Lemma gen_heap_alloc_gen σ σ' :
    σ' ##ₘ σ →
    gen_heap_ctx σ ==∗
    gen_heap_ctx (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ', meta_token l ⊤).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
      first by apply lookup_union_None.
  Qed.

  Lemma gen_heap_valid σ l q v : gen_heap_ctx σ -∗ l ↦{q} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iDestruct 1 as (m Hσm) "[Hσ _]". iIntros "Hl".
    rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_both_valid_discrete; auto.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_ctx σ -∗ l ↦ v1 ==∗ gen_heap_ctx (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iDestruct 1 as (m Hσm) "[Hσ Hm]".
    iIntros "Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%gen_heap_singleton_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree (v2:leibnizO _)))=> //.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iModIntro. iFrame "Hl". iExists m. rewrite to_gen_heap_insert. iFrame.
    iPureIntro. apply (elem_of_dom_2 (D:=gset L)) in Hl.
    rewrite dom_insert_L. set_solver.
  Qed.
End gen_heap.
