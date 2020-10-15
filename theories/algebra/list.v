From stdpp Require Export list.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.base_logic Require Import base_logic.
From iris Require Import options.

Section cofe.
Context {A : ofeT}.
Implicit Types l : list A.

Instance list_dist : Dist (list A) := λ n, Forall2 (dist n).

Lemma list_dist_lookup n l1 l2 : l1 ≡{n}≡ l2 ↔ ∀ i, l1 !! i ≡{n}≡ l2 !! i.
Proof. setoid_rewrite dist_option_Forall2. apply Forall2_lookup. Qed.

Global Instance cons_ne : NonExpansive2 (@cons A) := _.
Global Instance app_ne : NonExpansive2 (@app A) := _.
Global Instance length_ne n : Proper (dist n ==> (=)) (@length A) := _.
Global Instance tail_ne : NonExpansive (@tail A) := _.
Global Instance take_ne n : NonExpansive (@take A n) := _.
Global Instance drop_ne n : NonExpansive (@drop A n) := _.
Global Instance head_ne : NonExpansive (head (A:=A)).
Proof. destruct 1; by constructor. Qed.
Global Instance list_lookup_ne i : NonExpansive (lookup (M:=list A) i).
Proof. intros ????. by apply dist_option_Forall2, Forall2_lookup. Qed.
Global Instance list_lookup_total_ne `{!Inhabited A} i :
  NonExpansive (lookup_total (M:=list A) i).
Proof. intros ???. rewrite !list_lookup_total_alt. by intros ->. Qed.
Global Instance list_alter_ne n f i :
  Proper (dist n ==> dist n) f →
  Proper (dist n ==> dist n) (alter (M:=list A) f i) := _.
Global Instance list_insert_ne i : NonExpansive2 (insert (M:=list A) i) := _.
Global Instance list_inserts_ne i : NonExpansive2 (@list_inserts A i) := _.
Global Instance list_delete_ne i : NonExpansive (delete (M:=list A) i) := _.
Global Instance option_list_ne : NonExpansive (@option_list A).
Proof. intros ????; by apply Forall2_option_list, dist_option_Forall2. Qed.
Global Instance list_filter_ne n P `{∀ x, Decision (P x)} :
  Proper (dist n ==> iff) P →
  Proper (dist n ==> dist n) (filter (B:=list A) P) := _.
Global Instance replicate_ne n : NonExpansive (@replicate A n) := _.
Global Instance reverse_ne : NonExpansive (@reverse A) := _.
Global Instance last_ne : NonExpansive (@last A).
Proof. intros ????; by apply dist_option_Forall2, Forall2_last. Qed.
Global Instance resize_ne n : NonExpansive2 (@resize A n) := _.

Lemma list_dist_cons_inv_l n x l k :
  x :: l ≡{n}≡ k → ∃ y k', x ≡{n}≡ y ∧ l ≡{n}≡ k' ∧ k = y :: k'.
Proof. apply Forall2_cons_inv_l. Qed.
Lemma list_dist_cons_inv_r n l k y :
  l ≡{n}≡ y :: k → ∃ x l', x ≡{n}≡ y ∧ l' ≡{n}≡ k ∧ l = x :: l'.
Proof. apply Forall2_cons_inv_r. Qed.

Definition list_ofe_mixin : OfeMixin (list A).
Proof.
  split.
  - intros l k. rewrite equiv_Forall2 -Forall2_forall.
    split; induction 1; constructor; intros; try apply equiv_dist; auto.
  - apply _.
  - rewrite /dist /list_dist. eauto using Forall2_impl, dist_S.
Qed.
Canonical Structure listO := OfeT (list A) list_ofe_mixin.

(** To define [compl : chain (list A) → list A] we make use of the fact that
given a given chain [c0, c1, c2, ...] of lists, the list [c0] completely
determines the shape (i.e. the length) of all lists in the chain. So, the
[compl] operation is defined by structural recursion on [c0], and takes the
completion of the elements of all lists in the chain point-wise. We use [head]
and [tail] as the inverse of [cons]. *)
Fixpoint list_compl_go `{!Cofe A} (c0 : list A) (c : chain listO) : listO :=
  match c0 with
  | [] => []
  | x :: c0 => compl (chain_map (default x ∘ head) c) :: list_compl_go c0 (chain_map tail c)
  end.

Global Program Instance list_cofe `{!Cofe A} : Cofe listO :=
  {| compl c := list_compl_go (c 0) c |}.
Next Obligation.
  intros ? n c; rewrite /compl.
  assert (c 0 ≡{0}≡ c n) as Hc0 by (symmetry; apply chain_cauchy; lia).
  revert Hc0. generalize (c 0)=> c0. revert c.
  induction c0 as [|x c0 IH]=> c Hc0 /=.
  { by inversion Hc0. }
  apply list_dist_cons_inv_l in Hc0 as (x' & xs' & Hx & Hc0 & Hcn).
  rewrite Hcn. f_equiv.
  - by rewrite conv_compl /= Hcn /=.
  - rewrite IH /= ?Hcn //.
Qed.

Global Instance list_ofe_discrete : OfeDiscrete A → OfeDiscrete listO.
Proof. induction 2; constructor; try apply (discrete _); auto. Qed.

Global Instance nil_discrete : Discrete (@nil A).
Proof. inversion_clear 1; constructor. Qed.
Global Instance cons_discrete x l : Discrete x → Discrete l → Discrete (x :: l).
Proof. intros ??; inversion_clear 1; constructor; by apply discrete. Qed.

(** Internalized properties *)
Lemma list_equivI {M} l1 l2 : l1 ≡ l2 ⊣⊢@{uPredI M} ∀ i, l1 !! i ≡ l2 !! i.
Proof. uPred.unseal; constructor=> n x ?. apply list_dist_lookup. Qed.
End cofe.

Arguments listO : clear implicits.

(** Non-expansiveness of higher-order list functions and big-ops *)
Instance list_fmap_ne {A B : ofeT} (f : A → B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (fmap (M:=list) f).
Proof. intros Hf l k ?; by eapply Forall2_fmap, Forall2_impl; eauto. Qed.
Instance list_omap_ne {A B : ofeT} (f : A → option B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (omap (M:=list) f).
Proof.
  intros Hf. induction 1 as [|x1 x2 l1 l2 Hx Hl]; csimpl; [constructor|].
  destruct (Hf _ _ Hx); [f_equiv|]; auto.
Qed.
Instance imap_ne {A B : ofeT} (f : nat → A → B) n :
  (∀ i, Proper (dist n ==> dist n) (f i)) → Proper (dist n ==> dist n) (imap f).
Proof.
  intros Hf l1 l2 Hl. revert f Hf.
  induction Hl; intros f Hf; simpl; [constructor|f_equiv; naive_solver].
Qed.
Instance list_bind_ne {A B : ofeT} (f : A → list A) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (mbind f).
Proof. induction 2; simpl; [constructor|solve_proper]. Qed.
Instance list_join_ne {A : ofeT} : NonExpansive (mjoin (M:=list) (A:=A)).
Proof. induction 1; simpl; [constructor|solve_proper]. Qed.
Instance zip_with_ne {A B C : ofeT} (f : A → B → C) n :
  Proper (dist n ==> dist n ==> dist n) f →
  Proper (dist n ==> dist n ==> dist n) (zip_with f).
Proof. induction 2; destruct 1; simpl; [constructor..|f_equiv; [f_equiv|]; auto]. Qed.

Lemma big_opL_ne_2 `{Monoid M o} {A : ofeT} (f g : nat → A → M) l1 l2 n :
  l1 ≡{n}≡ l2 →
  (∀ k y1 y2,
    l1 !! k = Some y1 → l2 !! k = Some y2 → y1 ≡{n}≡ y2 → f k y1 ≡{n}≡ g k y2) →
  ([^o list] k ↦ y ∈ l1, f k y) ≡{n}≡ ([^o list] k ↦ y ∈ l2, g k y).
Proof.
  intros Hl Hf. apply big_opL_gen_proper_2; try (apply _ || done).
  { apply monoid_ne. }
  intros k. assert (l1 !! k ≡{n}≡ l2 !! k) as Hlk by (by f_equiv).
  destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
Qed.

Lemma big_sepL2_ne_2 {PROP : bi} {A B : ofeT}
    (Φ Ψ : nat → A → B → PROP) l1 l2 l1' l2' n :
  l1 ≡{n}≡ l1' → l2 ≡{n}≡ l2' →
  (∀ k y1 y1' y2 y2',
    l1 !! k = Some y1 → l1' !! k = Some y1' → y1 ≡{n}≡ y1' →
    l2 !! k = Some y2 → l2' !! k = Some y2' → y2 ≡{n}≡ y2' →
    Φ k y1 y2 ≡{n}≡ Ψ k y1' y2') →
  ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)%I ≡{n}≡ ([∗ list] k ↦ y1;y2 ∈ l1';l2', Ψ k y1 y2)%I.
Proof.
  intros Hl1 Hl2 Hf. rewrite !big_sepL2_alt. f_equiv.
  { do 2 f_equiv; by apply: length_ne. }
  apply big_opL_ne_2; [by f_equiv|].
  intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%lookup_zip_with_Some
    (?&?&[=<- <-]&?&?)%lookup_zip_with_Some [??]; naive_solver.
Qed.

(** Functor *)
Lemma list_fmap_ext_ne {A} {B : ofeT} (f g : A → B) (l : list A) n :
  (∀ x, f x ≡{n}≡ g x) → f <$> l ≡{n}≡ g <$> l.
Proof. intros Hf. by apply Forall2_fmap, Forall_Forall2, Forall_true. Qed.
Definition listO_map {A B} (f : A -n> B) : listO A -n> listO B :=
  OfeMor (fmap f : listO A → listO B).
Instance listO_map_ne A B : NonExpansive (@listO_map A B).
Proof. intros n f g ? l. by apply list_fmap_ext_ne. Qed.

Program Definition listOF (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := listO (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := listO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_equiv_ext=>y. apply oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_equiv_ext=>y; apply oFunctor_map_compose.
Qed.

Instance listOF_contractive F :
  oFunctorContractive F → oFunctorContractive (listOF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, oFunctor_map_contractive.
Qed.

(* CMRA. Only works if [A] has a unit! *)
Section cmra.
  Context {A : ucmraT}.
  Implicit Types l : list A.
  Local Arguments op _ _ !_ !_ / : simpl nomatch.

  Instance list_op : Op (list A) :=
    fix go l1 l2 := let _ : Op _ := @go in
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: l1, y :: l2 => x ⋅ y :: l1 ⋅ l2
    end.
  Instance list_pcore : PCore (list A) := λ l, Some (core <$> l).

  Instance list_valid : Valid (list A) := Forall (λ x, ✓ x).
  Instance list_validN : ValidN (list A) := λ n, Forall (λ x, ✓{n} x).

  Lemma cons_valid l x : ✓ (x :: l) ↔ ✓ x ∧ ✓ l.
  Proof. apply Forall_cons. Qed.
  Lemma cons_validN n l x : ✓{n} (x :: l) ↔ ✓{n} x ∧ ✓{n} l.
  Proof. apply Forall_cons. Qed.
  Lemma app_valid l1 l2 : ✓ (l1 ++ l2) ↔ ✓ l1 ∧ ✓ l2.
  Proof. apply Forall_app. Qed.
  Lemma app_validN n l1 l2 : ✓{n} (l1 ++ l2) ↔ ✓{n} l1 ∧ ✓{n} l2.
  Proof. apply Forall_app. Qed.

  Lemma list_lookup_valid l : ✓ l ↔ ∀ i, ✓ (l !! i).
  Proof.
    rewrite {1}/valid /list_valid Forall_lookup; split.
    - intros Hl i. by destruct (l !! i) as [x|] eqn:?; [apply (Hl i)|].
    - intros Hl i x Hi. move: (Hl i); by rewrite Hi.
  Qed.
  Lemma list_lookup_validN n l : ✓{n} l ↔ ∀ i, ✓{n} (l !! i).
  Proof.
    rewrite {1}/validN /list_validN Forall_lookup; split.
    - intros Hl i. by destruct (l !! i) as [x|] eqn:?; [apply (Hl i)|].
    - intros Hl i x Hi. move: (Hl i); by rewrite Hi.
  Qed.
  Lemma list_lookup_op l1 l2 i : (l1 ⋅ l2) !! i = l1 !! i ⋅ l2 !! i.
  Proof.
    revert i l2. induction l1 as [|x l1]; intros [|i] [|y l2];
      by rewrite /= ?left_id_L ?right_id_L.
  Qed.
  Lemma list_lookup_core l i : core l !! i = core (l !! i).
  Proof.
    rewrite /core /= list_lookup_fmap.
    destruct (l !! i); by rewrite /= ?Some_core.
  Qed.

  Lemma list_lookup_included l1 l2 : l1 ≼ l2 ↔ ∀ i, l1 !! i ≼ l2 !! i.
  Proof.
    split.
    { intros [l Hl] i. exists (l !! i). by rewrite Hl list_lookup_op. }
    revert l1. induction l2 as [|y l2 IH]=>-[|x l1] Hl.
    - by exists [].
    - destruct (Hl 0) as [[z|] Hz]; inversion Hz.
    - by exists (y :: l2).
    - destruct (IH l1) as [l3 ?]; first (intros i; apply (Hl (S i))).
      destruct (Hl 0) as [[z|] Hz]; inversion_clear Hz; simplify_eq/=.
      + exists (z :: l3); by constructor.
      + exists (core x :: l3); constructor; by rewrite ?cmra_core_r.
  Qed.

  Definition list_cmra_mixin : CmraMixin (list A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - intros n l l1 l2; rewrite !list_dist_lookup=> Hl i.
      by rewrite !list_lookup_op Hl.
    - intros n l1 l2 Hl; by rewrite /core /= Hl.
    - intros n l1 l2; rewrite !list_dist_lookup !list_lookup_validN=> Hl ? i.
      by rewrite -Hl.
    - intros l. rewrite list_lookup_valid. setoid_rewrite list_lookup_validN.
      setoid_rewrite cmra_valid_validN. naive_solver.
    - intros n x. rewrite !list_lookup_validN. auto using cmra_validN_S.
    - intros l1 l2 l3; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_op assoc.
    - intros l1 l2; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_op comm.
    - intros l; rewrite list_equiv_lookup=> i.
      by rewrite list_lookup_op list_lookup_core cmra_core_l.
    - intros l; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_core cmra_core_idemp.
    - intros l1 l2; rewrite !list_lookup_included=> Hl i.
      rewrite !list_lookup_core. by apply cmra_core_mono.
    - intros n l1 l2. rewrite !list_lookup_validN.
      setoid_rewrite list_lookup_op. eauto using cmra_validN_op_l.
    - intros n l.
      induction l as [|x l IH]=> -[|y1 l1] [|y2 l2] Hl Heq;
        (try by exfalso; inversion Heq).
      + by exists [], [].
      + exists [], (x :: l); inversion Heq; by repeat constructor.
      + exists (x :: l), []; inversion Heq; by repeat constructor.
      + destruct (IH l1 l2) as (l1'&l2'&?&?&?),
          (cmra_extend n x y1 y2) as (y1'&y2'&?&?&?);
          [by inversion_clear Heq; inversion_clear Hl..|].
        exists (y1' :: l1'), (y2' :: l2'); repeat constructor; auto.
  Qed.
  Canonical Structure listR := CmraT (list A) list_cmra_mixin.

  Global Instance list_unit : Unit (list A) := [].
  Definition list_ucmra_mixin : UcmraMixin (list A).
  Proof.
    split.
    - constructor.
    - by intros l.
    - by constructor.
  Qed.
  Canonical Structure listUR := UcmraT (list A) list_ucmra_mixin.

  Global Instance list_cmra_discrete : CmraDiscrete A → CmraDiscrete listR.
  Proof.
    split; [apply _|]=> l; rewrite list_lookup_valid list_lookup_validN=> Hl i.
    by apply cmra_discrete_valid.
  Qed.

  Lemma list_core_id' l : (∀ x, x ∈ l → CoreId x) → CoreId l.
  Proof.
    intros Hyp. constructor. apply list_equiv_lookup=> i.
    rewrite list_lookup_core.
    destruct (l !! i) eqn:E; last done.
    by eapply Hyp, elem_of_list_lookup_2.
  Qed.

  Global Instance list_core_id l : (∀ x : A, CoreId x) → CoreId l.
  Proof. intros Hyp; by apply list_core_id'. Qed.

  (** Internalized properties *)
  Lemma list_validI {M} l : ✓ l ⊣⊢@{uPredI M} ∀ i, ✓ (l !! i).
  Proof. uPred.unseal; constructor=> n x ?. apply list_lookup_validN. Qed.
End cmra.

Arguments listR : clear implicits.
Arguments listUR : clear implicits.

Instance list_singletonM {A : ucmraT} : SingletonM nat A (list A) := λ n x,
  replicate n ε ++ [x].

Section properties.
  Context {A : ucmraT}.
  Implicit Types l : list A.
  Implicit Types x y z : A.
  Local Arguments op _ _ !_ !_ / : simpl nomatch.
  Local Arguments cmra_op _ !_ !_ / : simpl nomatch.
  Local Arguments ucmra_op _ !_ !_ / : simpl nomatch.

  Lemma list_lookup_opM l mk i : (l ⋅? mk) !! i = l !! i ⋅ (mk ≫= (.!! i)).
  Proof. destruct mk; by rewrite /= ?list_lookup_op ?right_id_L. Qed.

  Global Instance list_op_nil_l : LeftId (=) (@nil A) op.
  Proof. done. Qed.
  Global Instance list_op_nil_r : RightId (=) (@nil A) op.
  Proof. by intros []. Qed.

  Lemma list_op_app l1 l2 l3 :
    (l1 ++ l3) ⋅ l2 = (l1 ⋅ take (length l1) l2) ++ (l3 ⋅ drop (length l1) l2).
  Proof.
    revert l2 l3.
    induction l1 as [|x1 l1]=> -[|x2 l2] [|x3 l3]; f_equal/=; auto.
  Qed.
  Lemma list_op_app_le l1 l2 l3 :
    length l2 ≤ length l1 → (l1 ++ l3) ⋅ l2 = (l1 ⋅ l2) ++ l3.
  Proof. intros ?. by rewrite list_op_app take_ge // drop_ge // right_id_L. Qed.

  Lemma list_lookup_validN_Some n l i x : ✓{n} l → l !! i ≡{n}≡ Some x → ✓{n} x.
  Proof. move=> /list_lookup_validN /(_ i)=> Hl Hi; move: Hl. by rewrite Hi. Qed.
  Lemma list_lookup_valid_Some l i x : ✓ l → l !! i ≡ Some x → ✓ x.
  Proof. move=> /list_lookup_valid /(_ i)=> Hl Hi; move: Hl. by rewrite Hi. Qed.

  Lemma list_length_op l1 l2 : length (l1 ⋅ l2) = max (length l1) (length l2).
  Proof. revert l2. induction l1; intros [|??]; f_equal/=; auto. Qed.

  Lemma replicate_valid n (x : A) : ✓ x → ✓ replicate n x.
  Proof. apply Forall_replicate. Qed.
  Global Instance list_singletonM_ne i :
    NonExpansive (@list_singletonM A i).
  Proof. intros n l1 l2 ?. apply Forall2_app; by repeat constructor. Qed.
  Global Instance list_singletonM_proper i :
    Proper ((≡) ==> (≡)) (list_singletonM i) := ne_proper _.

  Lemma elem_of_list_singletonM i z x : z ∈ ({[i := x]} : list A) → z = ε ∨ z = x.
  Proof.
    rewrite elem_of_app elem_of_list_singleton elem_of_replicate. naive_solver.
  Qed.
  Lemma list_lookup_singletonM i x : ({[ i := x ]} : list A) !! i = Some x.
  Proof. induction i; by f_equal/=. Qed.
  Lemma list_lookup_singletonM_lt i i' x:
    (i' < i)%nat → ({[ i := x ]} : list A) !! i' = Some ε.
  Proof. move: i'. induction i; intros [|i']; naive_solver auto with lia. Qed.
  Lemma list_lookup_singletonM_gt i i' x:
    (i < i')%nat → ({[ i := x ]} : list A) !! i' = None.
  Proof. move: i'. induction i; intros [|i']; naive_solver auto with lia. Qed.
  Lemma list_lookup_singletonM_ne i j x :
    i ≠ j →
    ({[ i := x ]} : list A) !! j = None ∨ ({[ i := x ]} : list A) !! j = Some ε.
  Proof. revert j; induction i; intros [|j]; naive_solver auto with lia. Qed.
  Lemma list_singletonM_validN n i x : ✓{n} ({[ i := x ]} : list A) ↔ ✓{n} x.
  Proof.
    rewrite list_lookup_validN. split.
    { move=> /(_ i). by rewrite list_lookup_singletonM. }
    intros Hx j; destruct (decide (i = j)); subst.
    - by rewrite list_lookup_singletonM.
    - destruct (list_lookup_singletonM_ne i j x) as [Hi|Hi]; first done;
        rewrite Hi; by try apply (ucmra_unit_validN (A:=A)).
  Qed.
  Lemma list_singletonM_valid  i x : ✓ ({[ i := x ]} : list A) ↔ ✓ x.
  Proof.
    rewrite !cmra_valid_validN. by setoid_rewrite list_singletonM_validN.
  Qed.
  Lemma list_singletonM_length i x : length {[ i := x ]} = S i.
  Proof.
    rewrite /singletonM /list_singletonM app_length replicate_length /=; lia.
  Qed.

  Lemma list_singletonM_core i (x : A) : core {[ i := x ]} ≡@{list A} {[ i := core x ]}.
  Proof.
    rewrite /singletonM /list_singletonM.
    by rewrite {1}/core /= fmap_app fmap_replicate (core_id_core ∅).
  Qed.
  Lemma list_singletonM_op i (x y : A) :
    {[ i := x ]} ⋅ {[ i := y ]} ≡@{list A} {[ i := x ⋅ y ]}.
  Proof.
    rewrite /singletonM /list_singletonM /=.
    induction i; constructor; rewrite ?left_id; auto.
  Qed.
  Lemma list_alter_singletonM f i x :
    alter f i ({[i := x]} : list A) = {[i := f x]}.
  Proof.
    rewrite /singletonM /list_singletonM /=. induction i; f_equal/=; auto.
  Qed.
  Global Instance list_singletonM_core_id i (x : A) :
    CoreId x → CoreId {[ i := x ]}.
  Proof. by rewrite !core_id_total list_singletonM_core=> ->. Qed.
  Lemma list_singletonM_snoc l x:
    {[length l := x]} ⋅ l ≡ l ++ [x].
  Proof. elim: l => //= ?? <-. by rewrite left_id. Qed.
  Lemma list_singletonM_included i x l:
    {[i := x]} ≼ l ↔ (∃ x', l !! i = Some x' ∧ x ≼ x').
  Proof.
    rewrite list_lookup_included. split.
    { move /(_ i). rewrite list_lookup_singletonM option_included_total.
      naive_solver. }
    intros (y&Hi&?) j. destruct (Nat.lt_total j i) as [?|[->|?]].
    - rewrite list_lookup_singletonM_lt //.
      destruct (lookup_lt_is_Some_2 l j) as [z Hz].
      { trans i; eauto using lookup_lt_Some. }
      rewrite Hz. by apply Some_included_2, ucmra_unit_least.
    - rewrite list_lookup_singletonM Hi. by apply Some_included_2.
    - rewrite list_lookup_singletonM_gt //. apply: ucmra_unit_least.
  Qed.

  (* Update *)
  Lemma list_singletonM_updateP (P : A → Prop) (Q : list A → Prop) x :
    x ~~>: P → (∀ y, P y → Q [y]) → [x] ~~>: Q.
  Proof.
    rewrite !cmra_total_updateP=> Hup HQ n lf /list_lookup_validN Hv.
    destruct (Hup n (default ε (lf !! 0))) as (y&?&Hv').
    { move: (Hv 0). by destruct lf; rewrite /= ?right_id. }
    exists [y]; split; first by auto.
    apply list_lookup_validN=> i.
    move: (Hv i) Hv'. by destruct i, lf; rewrite /= ?right_id.
  Qed.
  Lemma list_singletonM_updateP' (P : A → Prop) x :
    x ~~>: P → [x] ~~>: λ k, ∃ y, k = [y] ∧ P y.
  Proof. eauto using list_singletonM_updateP. Qed.
  Lemma list_singletonM_update x y : x ~~> y → [x] ~~> [y].
  Proof.
    rewrite !cmra_update_updateP; eauto using list_singletonM_updateP with subst.
  Qed.

  Lemma app_updateP (P1 P2 Q : list A → Prop) l1 l2 :
    l1 ~~>: P1 → l2 ~~>: P2 →
    (∀ k1 k2, P1 k1 → P2 k2 → length l1 = length k1 ∧ Q (k1 ++ k2)) →
    l1 ++ l2 ~~>: Q.
  Proof.
    rewrite !cmra_total_updateP=> Hup1 Hup2 HQ n lf.
    rewrite list_op_app app_validN=> -[??].
    destruct (Hup1 n (take (length l1) lf)) as (k1&?&?); auto.
    destruct (Hup2 n (drop (length l1) lf)) as (k2&?&?); auto.
    exists (k1 ++ k2). rewrite list_op_app app_validN.
    by destruct (HQ k1 k2) as [<- ?].
  Qed.
  Lemma app_update l1 l2 k1 k2 :
    length l1 = length k1 →
    l1 ~~> k1 → l2 ~~> k2 → l1 ++ l2 ~~> k1 ++ k2.
  Proof. rewrite !cmra_update_updateP; eauto using app_updateP with subst. Qed.

  Lemma cons_updateP (P1 : A → Prop) (P2 Q : list A → Prop) x l :
    x ~~>: P1 → l ~~>: P2 → (∀ y k, P1 y → P2 k → Q (y :: k)) → x :: l ~~>: Q.
  Proof.
    intros. eapply (app_updateP _ _ _ [x]);
      naive_solver eauto using list_singletonM_updateP'.
  Qed.
  Lemma cons_updateP' (P1 : A → Prop) (P2 : list A → Prop) x l :
    x ~~>: P1 → l ~~>: P2 → x :: l ~~>: λ k, ∃ y k', k = y :: k' ∧ P1 y ∧ P2 k'.
  Proof. eauto 10 using cons_updateP. Qed.
  Lemma cons_update x y l k : x ~~> y → l ~~> k → x :: l ~~> y :: k.
  Proof. rewrite !cmra_update_updateP; eauto using cons_updateP with subst. Qed.

  Lemma list_middle_updateP (P : A → Prop) (Q : list A → Prop) l1 x l2 :
    x ~~>: P → (∀ y, P y → Q (l1 ++ y :: l2)) → l1 ++ x :: l2 ~~>: Q.
  Proof.
    intros. eapply app_updateP.
    - by apply cmra_update_updateP.
    - by eapply cons_updateP', cmra_update_updateP.
    - naive_solver.
  Qed.
  Lemma list_middle_update l1 l2 x y : x ~~> y → l1 ++ x :: l2 ~~> l1 ++ y :: l2.
  Proof.
    rewrite !cmra_update_updateP=> ?; eauto using list_middle_updateP with subst.
  Qed.

(* FIXME
  Lemma list_middle_local_update l1 l2 x y ml :
    x ~l~> y @ ml ≫= (.!! length l1) →
    l1 ++ x :: l2 ~l~> l1 ++ y :: l2 @ ml.
  Proof.
    intros [Hxy Hxy']; split.
    - intros n; rewrite !list_lookup_validN=> Hl i; move: (Hl i).
      destruct (lt_eq_lt_dec i (length l1)) as [[?|?]|?]; subst.
      + by rewrite !list_lookup_opM !lookup_app_l.
      + rewrite !list_lookup_opM !list_lookup_middle // !Some_op_opM; apply (Hxy n).
      + rewrite !(cons_middle _ l1 l2) !assoc.
        rewrite !list_lookup_opM !lookup_app_r !app_length //=; lia.
    - intros n mk; rewrite !list_lookup_validN !list_dist_lookup => Hl Hl' i.
      move: (Hl i) (Hl' i).
      destruct (lt_eq_lt_dec i (length l1)) as [[?|?]|?]; subst.
      + by rewrite !list_lookup_opM !lookup_app_l.
      + rewrite !list_lookup_opM !list_lookup_middle // !Some_op_opM !inj_iff.
        apply (Hxy' n).
      + rewrite !(cons_middle _ l1 l2) !assoc.
        rewrite !list_lookup_opM !lookup_app_r !app_length //=; lia.
  Qed.
  Lemma list_singleton_local_update i x y ml :
    x ~l~> y @ ml ≫= (.!! i) → {[ i := x ]} ~l~> {[ i := y ]} @ ml.
  Proof. intros; apply list_middle_local_update. by rewrite replicate_length. Qed.
*)

  Lemma list_alloc_singletonM_local_update x l :
    ✓ x → (l, ε) ~l~> (l ++ [x], {[length l := x]}).
  Proof.
    move => ?.
    have -> : ({[length l := x]} ≡ {[length l := x]} ⋅ ε) by rewrite right_id.
    rewrite -list_singletonM_snoc. apply op_local_update => ??.
    rewrite list_singletonM_snoc app_validN cons_validN. split_and? => //; [| constructor].
    by apply cmra_valid_validN.
  Qed.

End properties.

(** Functor *)
Instance list_fmap_cmra_morphism {A B : ucmraT} (f : A → B)
  `{!CmraMorphism f} : CmraMorphism (fmap f : list A → list B).
Proof.
  split; try apply _.
  - intros n l. rewrite !list_lookup_validN=> Hl i. rewrite list_lookup_fmap.
    by apply (cmra_morphism_validN (fmap f : option A → option B)).
  - intros l. apply Some_proper. rewrite -!list_fmap_compose.
    apply list_fmap_equiv_ext, cmra_morphism_core, _.
  - intros l1 l2. apply list_equiv_lookup=>i.
    by rewrite list_lookup_op !list_lookup_fmap list_lookup_op cmra_morphism_op.
Qed.

Program Definition listURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := listUR (urFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg := listO_map (urFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, urFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_equiv_ext=>y. apply urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_equiv_ext=>y; apply urFunctor_map_compose.
Qed.

Instance listURF_contractive F :
  urFunctorContractive F → urFunctorContractive (listURF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, urFunctor_map_contractive.
Qed.

Program Definition listRF (F : urFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := listR (urFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := listO_map (urFunctor_map F fg)
|}.
Solve Obligations with apply listURF.

Instance listRF_contractive F :
  urFunctorContractive F → rFunctorContractive (listRF F).
Proof. apply listURF_contractive. Qed.
