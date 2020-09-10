From stdpp Require Import namespaces.
From iris.algebra Require Export gmap coPset local_updates.
From iris.algebra Require Import updates proofmode_classes.
From iris Require Import options.

(** The camera [namespace_map A] over a camera [A] provides the connectives
[namespace_map_data N a], which associates data [a : A] with a namespace [N],
and [namespace_map_token E], which says that no data has been associated with
the namespaces in the mask [E]. The important properties of this camera are:

- The lemma [namespace_map_token_union] enables one to split [namespace_map_token]
  w.r.t. disjoint union. That is, if we have [E1 ## E2], then we get
  [namespace_map_token (E1 ∪ E2) = namespace_map_token E1 ⋅ namespace_map_token E2]
- The lemma [namespace_map_alloc_update] provides a frame preserving update to
  associate data to a namespace [namespace_map_token E ~~> namespace_map_data N a]
  provided [↑N ⊆ E] and [✓ a]. *)

Record namespace_map (A : Type) := NamespaceMap {
  namespace_map_data_proj : gmap positive A;
  namespace_map_token_proj : coPset_disj
}.
Add Printing Constructor namespace_map.
Arguments NamespaceMap {_} _ _.
Arguments namespace_map_data_proj {_} _.
Arguments namespace_map_token_proj {_} _.
Instance: Params (@NamespaceMap) 1 := {}.
Instance: Params (@namespace_map_data_proj) 1 := {}.
Instance: Params (@namespace_map_token_proj) 1 := {}.

(** TODO: [positives_flatten] violates the namespace abstraction. *)
Definition namespace_map_data {A : cmraT} (N : namespace) (a : A) : namespace_map A :=
  NamespaceMap {[ positives_flatten N := a ]} ε.
Definition namespace_map_token {A : cmraT} (E : coPset) : namespace_map A :=
  NamespaceMap ∅ (CoPset E).
Instance: Params (@namespace_map_data) 2 := {}.

(* Ofe *)
Section ofe.
Context {A : ofeT}.
Implicit Types x y : namespace_map A.

Instance namespace_map_equiv : Equiv (namespace_map A) := λ x y,
  namespace_map_data_proj x ≡ namespace_map_data_proj y ∧
  namespace_map_token_proj x = namespace_map_token_proj y.
Instance namespace_map_dist : Dist (namespace_map A) := λ n x y,
  namespace_map_data_proj x ≡{n}≡ namespace_map_data_proj y ∧
  namespace_map_token_proj x = namespace_map_token_proj y.

Global Instance NamespaceMap_ne : NonExpansive2 (@NamespaceMap A).
Proof. by split. Qed.
Global Instance NamespaceMap_proper : Proper ((≡) ==> (=) ==> (≡)) (@NamespaceMap A).
Proof. by split. Qed.
Global Instance namespace_map_data_proj_ne: NonExpansive (@namespace_map_data_proj A).
Proof. by destruct 1. Qed.
Global Instance namespace_map_data_proj_proper :
  Proper ((≡) ==> (≡)) (@namespace_map_data_proj A).
Proof. by destruct 1. Qed.

Definition namespace_map_ofe_mixin : OfeMixin (namespace_map A).
Proof.
  by apply (iso_ofe_mixin
    (λ x, (namespace_map_data_proj x, namespace_map_token_proj x))).
Qed.
Canonical Structure namespace_mapO :=
  OfeT (namespace_map A) namespace_map_ofe_mixin.

Global Instance NamespaceMap_discrete a b :
  Discrete a → Discrete b → Discrete (NamespaceMap a b).
Proof. intros ?? [??] [??]; split; unfold_leibniz; by eapply discrete. Qed.
Global Instance namespace_map_ofe_discrete :
  OfeDiscrete A → OfeDiscrete namespace_mapO.
Proof. intros ? [??]; apply _. Qed.
End ofe.

Arguments namespace_mapO : clear implicits.

(* Camera *)
Section cmra.
Context {A : cmraT}.
Implicit Types a b : A.
Implicit Types x y : namespace_map A.

Global Instance namespace_map_data_ne i : NonExpansive (@namespace_map_data A i).
Proof. solve_proper. Qed.
Global Instance namespace_map_data_proper N :
  Proper ((≡) ==> (≡)) (@namespace_map_data A N).
Proof. solve_proper. Qed.
Global Instance namespace_map_data_discrete N a :
  Discrete a → Discrete (namespace_map_data N a).
Proof. intros. apply NamespaceMap_discrete; apply _. Qed.
Global Instance namespace_map_token_discrete E : Discrete (@namespace_map_token A E).
Proof. intros. apply NamespaceMap_discrete; apply _. Qed.

Instance namespace_map_valid : Valid (namespace_map A) := λ x,
  match namespace_map_token_proj x with
  | CoPset E =>
     ✓ (namespace_map_data_proj x) ∧
     (* dom (namespace_map_data_proj x) ⊥ E *)
     ∀ i, namespace_map_data_proj x !! i = None ∨ i ∉ E
  | CoPsetBot => False
  end.
Global Arguments namespace_map_valid !_ /.
Instance namespace_map_validN : ValidN (namespace_map A) := λ n x,
  match namespace_map_token_proj x with
  | CoPset E =>
     ✓{n} (namespace_map_data_proj x) ∧
     (* dom (namespace_map_data_proj x) ⊥ E *)
     ∀ i, namespace_map_data_proj x !! i = None ∨ i ∉ E
  | CoPsetBot => False
  end.
Global Arguments namespace_map_validN !_ /.
Instance namespace_map_pcore : PCore (namespace_map A) := λ x,
  Some (NamespaceMap (core (namespace_map_data_proj x)) ε).
Instance namespace_map_op : Op (namespace_map A) := λ x y,
  NamespaceMap (namespace_map_data_proj x ⋅ namespace_map_data_proj y)
               (namespace_map_token_proj x ⋅ namespace_map_token_proj y).

Definition namespace_map_valid_eq :
  valid = λ x, match namespace_map_token_proj x with
               | CoPset E =>
                  ✓ (namespace_map_data_proj x) ∧
                  (* dom (namespace_map_data_proj x) ⊥ E *)
                  ∀ i, namespace_map_data_proj x !! i = None ∨ i ∉ E
               | CoPsetBot => False
               end := eq_refl _.
Definition namespace_map_validN_eq :
  validN = λ n x, match namespace_map_token_proj x with
                  | CoPset E =>
                     ✓{n} (namespace_map_data_proj x) ∧
                     (* dom (namespace_map_data_proj x) ⊥ E *)
                     ∀ i, namespace_map_data_proj x !! i = None ∨ i ∉ E
                  | CoPsetBot => False
                  end := eq_refl _.

Lemma namespace_map_included x y :
  x ≼ y ↔
    namespace_map_data_proj x ≼ namespace_map_data_proj y ∧
    namespace_map_token_proj x ≼ namespace_map_token_proj y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (NamespaceMap z1 z2); split; auto.
Qed.

Lemma namespace_map_data_proj_validN n x : ✓{n} x → ✓{n} namespace_map_data_proj x.
Proof. by destruct x as [? [?|]]=> // -[??]. Qed.
Lemma namespace_map_token_proj_validN n x : ✓{n} x → ✓{n} namespace_map_token_proj x.
Proof. by destruct x as [? [?|]]=> // -[??]. Qed.

Lemma namespace_map_cmra_mixin : CmraMixin (namespace_map A).
Proof.
  apply cmra_total_mixin.
  - eauto.
  - by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  - solve_proper.
  - intros n [m1 [E1|]] [m2 [E2|]] [Hm ?]=> // -[??]; split; simplify_eq/=.
    + by rewrite -Hm.
    + intros i. by rewrite -(dist_None n) -Hm dist_None.
  - intros [m [E|]]; rewrite namespace_map_valid_eq namespace_map_validN_eq /=
      ?cmra_valid_validN; naive_solver eauto using O.
  - intros n [m [E|]]; rewrite namespace_map_validN_eq /=;
      naive_solver eauto using cmra_validN_S.
  - split; simpl; [by rewrite assoc|by rewrite assoc_L].
  - split; simpl; [by rewrite comm|by rewrite comm_L].
  - split; simpl; [by rewrite cmra_core_l|by rewrite left_id_L].
  - split; simpl; [by rewrite cmra_core_idemp|done].
  - intros ??; rewrite! namespace_map_included; intros [??].
    by split; simpl; apply: cmra_core_mono. (* FIXME: FIXME(Coq #6294): needs new unification *)
  - intros n [m1 [E1|]] [m2 [E2|]]=> //=; rewrite namespace_map_validN_eq /=.
    rewrite {1}/op /cmra_op /=. case_decide; last done.
    intros [Hm Hdisj]; split; first by eauto using cmra_validN_op_l.
    intros i. move: (Hdisj i). rewrite lookup_op.
    case: (m1 !! i)=> [a|]; last auto.
    move=> []. by case: (m2 !! i). set_solver.
  - intros n x y1 y2 ? [??]; simpl in *.
    destruct (cmra_extend n (namespace_map_data_proj x)
      (namespace_map_data_proj y1) (namespace_map_data_proj y2))
      as (m1&m2&?&?&?); auto using namespace_map_data_proj_validN.
    destruct (cmra_extend n (namespace_map_token_proj x)
      (namespace_map_token_proj y1) (namespace_map_token_proj y2))
      as (E1&E2&?&?&?); auto using namespace_map_token_proj_validN.
    by exists (NamespaceMap m1 E1), (NamespaceMap m2 E2).
Qed.
Canonical Structure namespace_mapR :=
  CmraT (namespace_map A) namespace_map_cmra_mixin.

Global Instance namespace_map_cmra_discrete :
  CmraDiscrete A → CmraDiscrete namespace_mapR.
Proof.
  split; first apply _.
  intros [m [E|]]; rewrite namespace_map_validN_eq namespace_map_valid_eq //=.
  by intros [?%cmra_discrete_valid ?].
Qed.

Instance namespace_map_empty : Unit (namespace_map A) := NamespaceMap ε ε.
Lemma namespace_map_ucmra_mixin : UcmraMixin (namespace_map A).
Proof.
  split; simpl.
  - rewrite namespace_map_valid_eq /=. split. apply ucmra_unit_valid. set_solver.
  - split; simpl; [by rewrite left_id|by rewrite left_id_L].
  - do 2 constructor; [apply (core_id_core _)|done].
Qed.
Canonical Structure namespace_mapUR :=
  UcmraT (namespace_map A) namespace_map_ucmra_mixin.

Global Instance namespace_map_data_core_id N a :
  CoreId a → CoreId (namespace_map_data N a).
Proof. do 2 constructor; simpl; auto. apply core_id_core, _. Qed.

Lemma namespace_map_data_valid N a : ✓ (namespace_map_data N a) ↔ ✓ a.
Proof. rewrite namespace_map_valid_eq /= singleton_valid. set_solver. Qed.
Lemma namespace_map_token_valid E : ✓ (namespace_map_token E).
Proof. rewrite namespace_map_valid_eq /=. split. done. by left. Qed.
Lemma namespace_map_data_op N a b :
  namespace_map_data N (a ⋅ b) = namespace_map_data N a ⋅ namespace_map_data N b.
Proof.
  by rewrite {2}/op /namespace_map_op /namespace_map_data /= singleton_op left_id_L.
Qed.
Lemma namespace_map_data_mono N a b :
  a ≼ b → namespace_map_data N a ≼ namespace_map_data N b.
Proof. intros [c ->]. rewrite namespace_map_data_op. apply cmra_included_l. Qed.
Global Instance is_op_namespace_map_data N a b1 b2 :
  IsOp a b1 b2 →
  IsOp' (namespace_map_data N a) (namespace_map_data N b1) (namespace_map_data N b2).
Proof. rewrite /IsOp' /IsOp=> ->. by rewrite namespace_map_data_op. Qed.

Lemma namespace_map_token_union E1 E2 :
  E1 ## E2 →
  namespace_map_token (E1 ∪ E2) = namespace_map_token E1 ⋅ namespace_map_token E2.
Proof.
  intros. by rewrite /op /namespace_map_op
    /namespace_map_token /= coPset_disj_union // left_id_L.
Qed.
Lemma namespace_map_token_difference E1 E2 :
  E1 ⊆ E2 →
   namespace_map_token E2 = namespace_map_token E1 ⋅ namespace_map_token (E2 ∖ E1).
Proof.
  intros. rewrite -namespace_map_token_union; last set_solver.
  by rewrite -union_difference_L.
Qed.
Lemma namespace_map_token_valid_op E1 E2 :
  ✓ (namespace_map_token E1 ⋅ namespace_map_token E2) ↔ E1 ## E2.
Proof.
  rewrite namespace_map_valid_eq /= {1}/op /cmra_op /=. case_decide; last done.
  split; [done|]; intros _. split.
  - by rewrite left_id.
  - intros i. rewrite lookup_op lookup_empty. auto.
Qed.

(** [↑N ⊆ E] is stronger than needed, just [positives_flatten N ∈ E] would be
sufficient. However, we do not have convenient infrastructure to prove the
latter, so we use the former. *)
Lemma namespace_map_alloc_update E N a :
  ↑N ⊆ E → ✓ a → namespace_map_token E ~~> namespace_map_data N a.
Proof.
  assert (positives_flatten N ∈ (↑N : coPset)).
  { rewrite nclose_eq. apply elem_coPset_suffixes.
    exists 1%positive. by rewrite left_id_L. }
  intros ??. apply cmra_total_update=> n [mf [Ef|]] //.
  rewrite namespace_map_validN_eq /= {1}/op /cmra_op /=. case_decide; last done.
  rewrite left_id_L {1}left_id. intros [Hmf Hdisj]; split.
  - destruct (Hdisj (positives_flatten N)) as [Hmfi|]; last set_solver.
    move: Hmfi. rewrite lookup_op lookup_empty left_id_L=> Hmfi.
    intros j. rewrite lookup_op.
    destruct (decide (positives_flatten N = j)) as [<-|].
    + rewrite Hmfi lookup_singleton right_id_L. by apply cmra_valid_validN.
    + by rewrite lookup_singleton_ne // left_id_L.
  - intros j. destruct (decide (positives_flatten N = j)); first set_solver.
    rewrite lookup_op lookup_singleton_ne //.
    destruct (Hdisj j) as [Hmfi|?]; last set_solver.
    move: Hmfi. rewrite lookup_op lookup_empty; auto.
Qed.
Lemma namespace_map_updateP P (Q : namespace_map A → Prop) N a :
  a ~~>: P →
  (∀ a', P a' → Q (namespace_map_data N a')) → namespace_map_data N a ~~>: Q.
Proof.
  intros Hup HP. apply cmra_total_updateP=> n [mf [Ef|]] //.
  rewrite namespace_map_validN_eq /= left_id_L. intros [Hmf Hdisj].
  destruct (Hup n (mf !! positives_flatten N)) as (a'&?&?).
  { move: (Hmf (positives_flatten N)).
    by rewrite lookup_op lookup_singleton Some_op_opM. }
  exists (namespace_map_data N a'); split; first by eauto.
  rewrite /= left_id_L. split.
  - intros j. destruct (decide (positives_flatten N = j)) as [<-|].
    + by rewrite lookup_op lookup_singleton Some_op_opM.
    + rewrite lookup_op lookup_singleton_ne // left_id_L.
      move: (Hmf j). rewrite lookup_op. eauto using cmra_validN_op_r.
  - intros j. move: (Hdisj j).
    rewrite !lookup_op !op_None !lookup_singleton_None. naive_solver.
Qed.
Lemma namespace_map_update N a b :
  a ~~> b → namespace_map_data N a ~~> namespace_map_data N b.
Proof.
  rewrite !cmra_update_updateP. eauto using namespace_map_updateP with subst.
Qed.
End cmra.

Arguments namespace_mapR : clear implicits.
Arguments namespace_mapUR : clear implicits.
