From stdpp Require Import countable fin_sets functions.
From iris.algebra Require Export big_op.
From iris.algebra Require Import list gmap.
From iris.bi Require Import derived_laws_later.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.

(** Notations for unary variants *)
Notation "'[∗' 'list]' k ↦ x ∈ l , P" :=
  (big_opL bi_sep (λ k x, P) l) : bi_scope.
Notation "'[∗' 'list]' x ∈ l , P" :=
  (big_opL bi_sep (λ _ x, P) l) : bi_scope.
Notation "'[∗]' Ps" := (big_opL bi_sep (λ _ x, x) Ps) : bi_scope.

Notation "'[∧' 'list]' k ↦ x ∈ l , P" :=
  (big_opL bi_and (λ k x, P) l) : bi_scope.
Notation "'[∧' 'list]' x ∈ l , P" :=
  (big_opL bi_and (λ _ x, P) l) : bi_scope.
Notation "'[∧]' Ps" := (big_opL bi_and (λ _ x, x) Ps) : bi_scope.

Notation "'[∨' 'list]' k ↦ x ∈ l , P" :=
  (big_opL bi_or (λ k x, P) l) : bi_scope.
Notation "'[∨' 'list]' x ∈ l , P" :=
  (big_opL bi_or (λ _ x, P) l) : bi_scope.
Notation "'[∨]' Ps" := (big_opL bi_or (λ _ x, x) Ps) : bi_scope.

Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM bi_sep (λ k x, P) m) : bi_scope.
Notation "'[∗' 'map]' x ∈ m , P" := (big_opM bi_sep (λ _ x, P) m) : bi_scope.

Notation "'[∗' 'set]' x ∈ X , P" := (big_opS bi_sep (λ x, P) X) : bi_scope.

Notation "'[∗' 'mset]' x ∈ X , P" := (big_opMS bi_sep (λ x, P) X) : bi_scope.

(** Definitions and notations for binary variants *)
(** A version of the separating big operator that ranges over two lists. This
version also ensures that both lists have the same length. Although this version
can be defined in terms of the unary using a [zip] (see [big_sepL2_alt]), we do
not define it that way to get better computational behavior (for [simpl]). *)
Fixpoint big_sepL2 {PROP : bi} {A B}
    (Φ : nat → A → B → PROP) (l1 : list A) (l2 : list B) : PROP :=
  match l1, l2 with
  | [], [] => emp
  | x1 :: l1, x2 :: l2 => Φ 0 x1 x2 ∗ big_sepL2 (λ n, Φ (S n)) l1 l2
  | _, _ => False
  end%I.
Global Instance: Params (@big_sepL2) 3 := {}.
Global Arguments big_sepL2 {PROP A B} _ !_ !_ /.
Typeclasses Opaque big_sepL2.
Notation "'[∗' 'list]' k ↦ x1 ; x2 ∈ l1 ; l2 , P" :=
  (big_sepL2 (λ k x1 x2, P) l1 l2) : bi_scope.
Notation "'[∗' 'list]' x1 ; x2 ∈ l1 ; l2 , P" :=
  (big_sepL2 (λ _ x1 x2, P) l1 l2) : bi_scope.

Definition big_sepM2_def {PROP : bi} `{Countable K} {A B}
    (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B) : PROP :=
  (⌜ ∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k) ⌝ ∧
   [∗ map] k ↦ xy ∈ map_zip m1 m2, Φ k xy.1 xy.2)%I.
Definition big_sepM2_aux : seal (@big_sepM2_def). Proof. by eexists. Qed.
Definition big_sepM2 := big_sepM2_aux.(unseal).
Global Arguments big_sepM2 {PROP K _ _ A B} _ _ _.
Definition big_sepM2_eq : @big_sepM2 = _ := big_sepM2_aux.(seal_eq).
Global Instance: Params (@big_sepM2) 6 := {}.
Notation "'[∗' 'map]' k ↦ x1 ; x2 ∈ m1 ; m2 , P" :=
  (big_sepM2 (λ k x1 x2, P) m1 m2) : bi_scope.
Notation "'[∗' 'map]' x1 ; x2 ∈ m1 ; m2 , P" :=
  (big_sepM2 (λ _ x1 x2, P) m1 m2) : bi_scope.

(** * Properties *)
Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

(** ** Big ops over lists *)
Section sep_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_sepL_nil Φ : ([∗ list] k↦y ∈ nil, Φ k y) ⊣⊢ emp.
  Proof. done. Qed.
  Lemma big_sepL_nil' P `{!Affine P} Φ : P ⊢ [∗ list] k↦y ∈ nil, Φ k y.
  Proof. apply: affine. Qed.
  Lemma big_sepL_cons Φ x l :
    ([∗ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∗ [∗ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_sepL_singleton Φ x : ([∗ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_sepL_app Φ l1 l2 :
    ([∗ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∗ list] k↦y ∈ l1, Φ k y) ∗ ([∗ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.

  Lemma big_sepL_submseteq `{BiAffine PROP} (Φ : A → PROP) l1 l2 :
    l1 ⊆+ l2 → ([∗ list] y ∈ l2, Φ y) ⊢ [∗ list] y ∈ l1, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. by rewrite big_sepL_app sep_elim_l.
  Qed.

  (** The lemmas [big_sepL_mono], [big_sepL_ne] and [big_sepL_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_sepL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_sepL_ne Φ Ψ l n :
    (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y)%I ≡{n}≡ ([∗ list] k ↦ y ∈ l, Ψ k y)%I.
  Proof. apply big_opL_ne. Qed.
  Lemma big_sepL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∗ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opL] instances. *)
  Global Instance big_sepL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_sepL_mono; intros; apply Hf. Qed.
  Global Instance big_sepL_id_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_sep PROP) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Lemma big_sepL_emp l : ([∗ list] k↦y ∈ l, emp) ⊣⊢@{PROP} emp.
  Proof. by rewrite big_opL_unit. Qed.

  Lemma big_sepL_insert_acc Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ ([∗ list] k↦y ∈ <[i:=y]>l, Φ k y)).
  Proof.
    intros Hli. assert (i ≤ length l) by eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(take_drop_middle l i x) // big_sepL_app /=.
    rewrite Nat.add_0_r take_length_le //.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. apply sep_mono_r, forall_intro=> y.
    rewrite insert_app_r_alt ?take_length_le //.
    rewrite Nat.sub_diag /=. apply wand_intro_l.
    rewrite assoc !(comm _ (Φ _ _)) -assoc big_sepL_app /=.
    by rewrite Nat.add_0_r take_length_le.
  Qed.

  Lemma big_sepL_lookup_acc Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ list] k↦y ∈ l, Φ k y)).
  Proof. intros. by rewrite {1}big_sepL_insert_acc // (forall_elim x) list_insert_id. Qed.

  Lemma big_sepL_lookup Φ l i x `{!Absorbing (Φ i x)} :
    l !! i = Some x → ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof. intros. rewrite big_sepL_lookup_acc //. by rewrite sep_elim_l. Qed.

  Lemma big_sepL_elem_of (Φ : A → PROP) l x `{!Absorbing (Φ x)} :
    x ∈ l → ([∗ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup. by eapply (big_sepL_lookup (λ _, Φ)).
  Qed.

  Lemma big_sepL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∗ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∗ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_sepL_omap {B} (f : A → option B) (Φ : B → PROP) l :
    ([∗ list] y ∈ omap f l, Φ y) ⊣⊢ ([∗ list] y ∈ l, from_option Φ emp (f y)).
  Proof. by rewrite big_opL_omap. Qed.

  Lemma big_sepL_bind {B} (f : A → list B) (Φ : B → PROP) l :
    ([∗ list] y ∈ l ≫= f, Φ y) ⊣⊢ ([∗ list] x ∈ l, [∗ list] y ∈ f x, Φ y).
  Proof. by rewrite big_opL_bind. Qed.

  Lemma big_sepL_sep Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ list] k↦x ∈ l, Φ k x) ∗ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_op. Qed.

  Lemma big_sepL_and Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊢ ([∗ list] k↦x ∈ l, Φ k x) ∧ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. auto using and_intro, big_sepL_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepL_persistently `{BiAffine PROP} Φ l :
    <pers> ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ [∗ list] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_intuitionistically_forall Φ l :
    □ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x) ⊢ [∗ list] k↦x ∈ l, Φ k x.
  Proof.
    revert Φ. induction l as [|x l IH]=> Φ /=; [by apply (affine _)|].
    rewrite intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
      by rewrite intuitionistically_elim.
    - rewrite -IH. f_equiv.
      apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL_forall `{BiAffine PROP} Φ l :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepL_lookup. }
    rewrite -big_sepL_intuitionistically_forall. setoid_rewrite pure_impl_forall.
    by rewrite intuitionistic_intuitionistically.
  Qed.

  Lemma big_sepL_impl Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x) -∗
    □ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ list] k↦x ∈ l, Ψ k x.
  Proof.
    apply wand_intro_l. rewrite big_sepL_intuitionistically_forall -big_sepL_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepL_dup P `{!Affine P} l :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ list] k↦x ∈ l, P.
  Proof.
    apply wand_intro_l.
    induction l as [|x l IH]=> /=; first by apply: affine.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepL_delete Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y)
    ⊣⊢ Φ i x ∗ [∗ list] k↦y ∈ l, if decide (k = i) then emp else Φ k y.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // !big_sepL_app /= Nat.add_0_r.
    rewrite take_length_le; last eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite decide_True // left_id.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. do 2 f_equiv.
    - apply big_sepL_proper=> k y Hk. apply lookup_lt_Some in Hk.
      rewrite take_length in Hk. by rewrite decide_False; last lia.
    - apply big_sepL_proper=> k y _. by rewrite decide_False; last lia.
  Qed.

  Lemma big_sepL_delete' `{!BiAffine PROP} Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗ list] k↦y ∈ l, ⌜ k ≠ i ⌝ → Φ k y.
  Proof.
    intros. rewrite big_sepL_delete //. (do 2 f_equiv)=> k y.
    rewrite -decide_emp. by repeat case_decide.
  Qed.

  Lemma big_sepL_replicate l P :
    [∗] replicate (length l) P ⊣⊢ [∗ list] y ∈ l, P.
  Proof. induction l as [|x l]=> //=; by f_equiv. Qed.

  Lemma big_sepL_later `{BiAffine PROP} Φ l :
    ▷ ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_sepL_later_2 Φ l :
    ([∗ list] k↦x ∈ l, ▷ Φ k x) ⊢ ▷ [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.

  Lemma big_sepL_laterN `{BiAffine PROP} Φ n l :
    ▷^n ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_sepL_laterN_2 Φ n l :
    ([∗ list] k↦x ∈ l, ▷^n Φ k x) ⊢ ▷^n [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.

  Global Instance big_sepL_nil_persistent Φ :
    Persistent ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_persistent Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_persistent_id Ps :
    TCForall Persistent Ps → Persistent ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.

  Global Instance big_sepL_nil_affine Φ :
    Affine ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_affine Φ l :
    (∀ k x, Affine (Φ k x)) → Affine ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_affine_id Ps : TCForall Affine Ps → Affine ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.

  Global Instance big_sepL_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_timeless `{!Timeless (emp%I : PROP)} Φ l :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_timeless_id `{!Timeless (emp%I : PROP)} Ps :
    TCForall Timeless Ps → Timeless ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.
End sep_list.

Section sep_list_more.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.
  (* Some lemmas depend on the generalized versions of the above ones. *)

  Lemma big_sepL_zip_with {B C} Φ f (l1 : list B) (l2 : list C) :
    ([∗ list] k↦x ∈ zip_with f l1 l2, Φ k x)
    ⊣⊢ ([∗ list] k↦x ∈ l1, if l2 !! k is Some y then Φ k (f x y) else emp).
  Proof.
    revert Φ l2; induction l1 as [|x l1 IH]=> Φ [|y l2] //=.
    - by rewrite big_sepL_emp left_id.
    - by rewrite IH.
  Qed.
End sep_list_more.

Lemma big_sepL2_alt {A B} (Φ : nat → A → B → PROP) l1 l2 :
  ([∗ list] k↦y1;y2 ∈ l1; l2, Φ k y1 y2)
  ⊣⊢ ⌜ length l1 = length l2 ⌝ ∧ [∗ list] k ↦ y ∈ zip l1 l2, Φ k (y.1) (y.2).
Proof.
  apply (anti_symm _).
  - apply and_intro.
    + revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2] /=;
        auto using pure_intro, False_elim.
      rewrite IH sep_elim_r. apply pure_mono; auto.
    + revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2] /=;
        auto using pure_intro, False_elim.
      by rewrite IH.
  - apply pure_elim_l=> /Forall2_same_length Hl. revert Φ.
    induction Hl as [|x1 l1 x2 l2 _ _ IH]=> Φ //=. by rewrite -IH.
Qed.

(** ** Big ops over two lists *)
Section sep_list2.
  Context {A B : Type}.
  Implicit Types Φ Ψ : nat → A → B → PROP.

  Lemma big_sepL2_nil Φ : ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2) ⊣⊢ emp.
  Proof. done. Qed.
  Lemma big_sepL2_nil' P `{!Affine P} Φ : P ⊢ [∗ list] k↦y1;y2 ∈ [];[], Φ k y1 y2.
  Proof. apply: affine. Qed.
  Lemma big_sepL2_nil_inv_l Φ l2 :
    ([∗ list] k↦y1;y2 ∈ []; l2, Φ k y1 y2) -∗ ⌜l2 = []⌝.
  Proof. destruct l2; simpl; auto using False_elim, pure_intro. Qed.
  Lemma big_sepL2_nil_inv_r Φ l1 :
    ([∗ list] k↦y1;y2 ∈ l1; [], Φ k y1 y2) -∗ ⌜l1 = []⌝.
  Proof. destruct l1; simpl; auto using False_elim, pure_intro. Qed.

  Lemma big_sepL2_cons Φ x1 x2 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ x1 :: l1; x2 :: l2, Φ k y1 y2)
    ⊣⊢ Φ 0 x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1;l2, Φ (S k) y1 y2.
  Proof. done. Qed.
  Lemma big_sepL2_cons_inv_l Φ x1 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ x1 :: l1; l2, Φ k y1 y2) -∗
    ∃ x2 l2', ⌜ l2 = x2 :: l2' ⌝ ∧
              Φ 0 x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1;l2', Φ (S k) y1 y2.
  Proof.
    destruct l2 as [|x2 l2]; simpl; auto using False_elim.
    by rewrite -(exist_intro x2) -(exist_intro l2) pure_True // left_id.
  Qed.
  Lemma big_sepL2_cons_inv_r Φ x2 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1; x2 :: l2, Φ k y1 y2) -∗
    ∃ x1 l1', ⌜ l1 = x1 :: l1' ⌝ ∧
              Φ 0 x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1';l2, Φ (S k) y1 y2.
  Proof.
    destruct l1 as [|x1 l1]; simpl; auto using False_elim.
    by rewrite -(exist_intro x1) -(exist_intro l1) pure_True // left_id.
  Qed.

  Lemma big_sepL2_singleton Φ x1 x2 :
    ([∗ list] k↦y1;y2 ∈ [x1];[x2], Φ k y1 y2) ⊣⊢ Φ 0 x1 x2.
  Proof. by rewrite /= right_id. Qed.

  Lemma big_sepL2_length Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1; l2, Φ k y1 y2) -∗ ⌜ length l1 = length l2 ⌝.
  Proof. by rewrite big_sepL2_alt and_elim_l. Qed.

  Lemma big_sepL2_app Φ l1 l2 l1' l2' :
    ([∗ list] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k) y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2).
  Proof.
    apply wand_intro_r. revert Φ l1'. induction l1 as [|x1 l1 IH]=> Φ -[|x1' l1'] /=.
    - by rewrite left_id.
    - rewrite left_absorb. apply False_elim.
    - rewrite left_absorb. apply False_elim.
    - by rewrite -assoc IH.
  Qed.
  Lemma big_sepL2_app_inv_l Φ l1' l1'' l2 :
    ([∗ list] k↦y1;y2 ∈ l1' ++ l1''; l2, Φ k y1 y2) -∗
    ∃ l2' l2'', ⌜ l2 = l2' ++ l2'' ⌝ ∧
                ([∗ list] k↦y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
                ([∗ list] k↦y1;y2 ∈ l1'';l2'', Φ (length l1' + k) y1 y2).
  Proof.
    rewrite -(exist_intro (take (length l1') l2))
      -(exist_intro (drop (length l1') l2)) take_drop pure_True // left_id.
    revert Φ l2. induction l1' as [|x1 l1' IH]=> Φ -[|x2 l2] /=;
       [by rewrite left_id|by rewrite left_id|apply False_elim|].
    by rewrite IH -assoc.
  Qed.
  Lemma big_sepL2_app_inv_r Φ l1 l2' l2'' :
    ([∗ list] k↦y1;y2 ∈ l1; l2' ++ l2'', Φ k y1 y2) -∗
    ∃ l1' l1'', ⌜ l1 = l1' ++ l1'' ⌝ ∧
                ([∗ list] k↦y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
                ([∗ list] k↦y1;y2 ∈ l1'';l2'', Φ (length l2' + k) y1 y2).
  Proof.
    rewrite -(exist_intro (take (length l2') l1))
      -(exist_intro (drop (length l2') l1)) take_drop pure_True // left_id.
    revert Φ l1. induction l2' as [|x2 l2' IH]=> Φ -[|x1 l1] /=;
       [by rewrite left_id|by rewrite left_id|apply False_elim|].
    by rewrite IH -assoc.
  Qed.
  Lemma big_sepL2_app_inv Φ l1 l2 l1' l2' :
    length l1 = length l1' →
    ([∗ list] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ∗
    ([∗ list] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k)%nat y1 y2).
  Proof.
    revert Φ l1'. induction l1 as [|x1 l1 IH]=> Φ -[|x1' l1'] //= ?; simplify_eq.
    - by rewrite left_id.
    - by rewrite -assoc IH.
  Qed.

  (** The lemmas [big_sepL2_mono], [big_sepL2_ne] and [big_sepL2_proper] are more
  generic than the instances as they also give [li !! k = Some yi] in the premise. *)
  Lemma big_sepL2_mono Φ Ψ l1 l2 :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊢ Ψ k y1 y2) →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ [∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros H. rewrite !big_sepL2_alt. f_equiv. apply big_sepL_mono=> k [y1 y2].
    rewrite lookup_zip_with=> ?; simplify_option_eq; auto.
  Qed.
  Lemma big_sepL2_ne Φ Ψ l1 l2 n :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ≡{n}≡ Ψ k y1 y2) →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)%I ≡{n}≡ ([∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2)%I.
  Proof.
    intros H. rewrite !big_sepL2_alt. f_equiv. apply big_sepL_ne=> k [y1 y2].
    rewrite lookup_zip_with=> ?; simplify_option_eq; auto.
  Qed.
  Lemma big_sepL2_proper Φ Ψ l1 l2 :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊣⊢ Ψ k y1 y2) →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ [∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros; apply (anti_symm _);
      apply big_sepL2_mono; auto using equiv_entails, equiv_entails_sym.
  Qed.
  Lemma big_sepL2_proper_2 `{!Equiv A, !Equiv B} Φ Ψ l1 l2 l1' l2' :
    l1 ≡ l1' → l2 ≡ l2' →
    (∀ k y1 y1' y2 y2',
      l1 !! k = Some y1 → l1' !! k = Some y1' → y1 ≡ y1' →
      l2 !! k = Some y2 → l2' !! k = Some y2' → y2 ≡ y2' →
      Φ k y1 y2 ⊣⊢ Ψ k y1' y2') →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ [∗ list] k ↦ y1;y2 ∈ l1';l2', Ψ k y1 y2.
  Proof.
    intros Hl1 Hl2 Hf. rewrite !big_sepL2_alt. f_equiv.
    { do 2 f_equiv; by apply length_proper. }
    apply big_opL_proper_2; [by f_equiv|].
    intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%lookup_zip_with_Some
      (?&?&[=<- <-]&?&?)%lookup_zip_with_Some [??]; naive_solver.
  Qed.

  Global Instance big_sepL2_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n)))
      ==> (=) ==> (=) ==> (dist n))
           (big_sepL2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepL2_ne; intros; apply Hf. Qed.
  Global Instance big_sepL2_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
      ==> (=) ==> (=) ==> (⊢))
           (big_sepL2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepL2_mono; intros; apply Hf. Qed.
  Global Instance big_sepL2_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊣⊢)))
      ==> (=) ==> (=) ==> (⊣⊢))
           (big_sepL2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepL2_proper; intros; apply Hf. Qed.

  Lemma big_sepL2_insert_acc Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (∀ y1 y2, Φ i y1 y2 -∗ ([∗ list] k↦y1;y2 ∈ <[i:=y1]>l1;<[i:=y2]>l2, Φ k y1 y2)).
  Proof.
    intros Hl1 Hl2. rewrite big_sepL2_alt. apply pure_elim_l=> Hl.
    rewrite {1}big_sepL_insert_acc; last by rewrite lookup_zip_with; simplify_option_eq.
    apply sep_mono_r. apply forall_intro => y1. apply forall_intro => y2.
    rewrite big_sepL2_alt !insert_length pure_True // left_id -insert_zip_with.
    by rewrite (forall_elim (y1, y2)).
  Qed.

  Lemma big_sepL2_lookup_acc Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (Φ i x1 x2 -∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)).
  Proof.
    intros. rewrite {1}big_sepL2_insert_acc // (forall_elim x1) (forall_elim x2).
    by rewrite !list_insert_id.
  Qed.

  Lemma big_sepL2_lookup Φ l1 l2 i x1 x2 `{!Absorbing (Φ i x1 x2)} :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ Φ i x1 x2.
  Proof. intros. rewrite big_sepL2_lookup_acc //. by rewrite sep_elim_l. Qed.

  Lemma big_sepL2_fmap_l {A'} (f : A → A') (Φ : nat → A' → B → PROP) l1 l2 :
    ([∗ list] k↦y1;y2 ∈ f <$> l1; l2, Φ k y1 y2)
    ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k (f y1) y2).
  Proof.
    rewrite !big_sepL2_alt fmap_length zip_with_fmap_l zip_with_zip big_sepL_fmap.
    by f_equiv; f_equiv=> k [??].
  Qed.
  Lemma big_sepL2_fmap_r {B'} (g : B → B') (Φ : nat → A → B' → PROP) l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1; g <$> l2, Φ k y1 y2)
    ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 (g y2)).
  Proof.
    rewrite !big_sepL2_alt fmap_length zip_with_fmap_r zip_with_zip big_sepL_fmap.
    by f_equiv; f_equiv=> k [??].
  Qed.

  Lemma big_sepL2_reverse_2 (Φ : A → B → PROP) l1 l2 :
    ([∗ list] y1;y2 ∈ l1;l2, Φ y1 y2) ⊢ ([∗ list] y1;y2 ∈ reverse l1;reverse l2, Φ y1 y2).
  Proof.
    revert l2. induction l1 as [|x1 l1 IH]; intros [|x2 l2]; simpl; auto using False_elim.
    rewrite !reverse_cons (comm bi_sep) IH.
    by rewrite (big_sepL2_app _ _ [x1] _ [x2]) big_sepL2_singleton wand_elim_l.
  Qed.
  Lemma big_sepL2_reverse (Φ : A → B → PROP) l1 l2 :
    ([∗ list] y1;y2 ∈ reverse l1;reverse l2, Φ y1 y2) ⊣⊢ ([∗ list] y1;y2 ∈ l1;l2, Φ y1 y2).
  Proof. apply (anti_symm _); by rewrite big_sepL2_reverse_2 ?reverse_involutive. Qed.

  Lemma big_sepL2_replicate_l l x Φ n :
    length l = n →
    ([∗ list] k↦x1;x2 ∈ replicate n x; l, Φ k x1 x2) ⊣⊢ [∗ list] k↦x2 ∈ l, Φ k x x2.
  Proof. intros <-. revert Φ. induction l as [|y l IH]=> //= Φ. by rewrite IH. Qed.
  Lemma big_sepL2_replicate_r l x Φ n :
    length l = n →
    ([∗ list] k↦x1;x2 ∈ l;replicate n x, Φ k x1 x2) ⊣⊢ [∗ list] k↦x1 ∈ l, Φ k x1 x.
  Proof. intros <-. revert Φ. induction l as [|y l IH]=> //= Φ. by rewrite IH. Qed.

  Lemma big_sepL2_sep Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y1 y2)
    ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
  Proof.
    rewrite !big_sepL2_alt big_sepL_sep !persistent_and_affinely_sep_l.
    rewrite -assoc (assoc _ _ (<affine> _)%I). rewrite -(comm bi_sep (<affine> _)%I).
    rewrite -assoc (assoc _ _ (<affine> _)%I) -!persistent_and_affinely_sep_l.
    by rewrite affinely_and_r persistent_and_affinely_sep_l idemp.
  Qed.

  Lemma big_sepL2_and Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∧ Ψ k y1 y2)
    ⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∧ ([∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
  Proof. auto using and_intro, big_sepL2_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepL2_persistently `{BiAffine PROP} Φ l1 l2 :
    <pers> ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)
    ⊣⊢ [∗ list] k↦y1;y2 ∈ l1;l2, <pers> (Φ k y1 y2).
  Proof.
    by rewrite !big_sepL2_alt persistently_and persistently_pure big_sepL_persistently.
  Qed.

  Lemma big_sepL2_intuitionistically_forall Φ l1 l2 :
    length l1 = length l2 →
    □ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2) ⊢
    [∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2.
  Proof.
    revert l2 Φ. induction l1 as [|x1 l1 IH]=> -[|x2 l2] Φ ?; simplify_eq/=.
    { by apply (affine _). }
    rewrite intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim 0) (forall_elim x1) (forall_elim x2).
      by rewrite !pure_True // !True_impl intuitionistically_elim.
    - rewrite -IH //. f_equiv.
      by apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL2_forall `{BiAffine PROP} Φ l1 l2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      ⌜length l1 = length l2⌝
      ∧ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2).
  Proof.
    intros. apply (anti_symm _).
    - apply and_intro; [apply big_sepL2_length|].
      apply forall_intro=> k. apply forall_intro=> x1. apply forall_intro=> x2.
      do 2 (apply impl_intro_l; apply pure_elim_l=> ?). by apply :big_sepL2_lookup.
    - apply pure_elim_l=> ?. rewrite -big_sepL2_intuitionistically_forall //.
      repeat setoid_rewrite pure_impl_forall.
      by rewrite intuitionistic_intuitionistically.
  Qed.

  Lemma big_sepL2_impl Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    □ (∀ k x1 x2,
      ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2) -∗
    [∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    rewrite -(idemp bi_and (big_sepL2 _ _ _)) {1}big_sepL2_length.
    apply pure_elim_l=> ?. rewrite big_sepL2_intuitionistically_forall //.
    apply bi.wand_intro_l. rewrite -big_sepL2_sep. by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepL2_later_1 `{BiAffine PROP} Φ l1 l2 :
    (▷ [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ◇ [∗ list] k↦y1;y2 ∈ l1;l2, ▷ Φ k y1 y2.
  Proof.
    rewrite !big_sepL2_alt later_and big_sepL_later (timeless ⌜ _ ⌝%I).
    rewrite except_0_and. auto using and_mono, except_0_intro.
  Qed.

  Lemma big_sepL2_later_2 Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, ▷ Φ k y1 y2) ⊢ ▷ [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2.
  Proof.
    rewrite !big_sepL2_alt later_and big_sepL_later_2.
    auto using and_mono, later_intro.
  Qed.

  Lemma big_sepL2_laterN_2 Φ n l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, ▷^n Φ k y1 y2) ⊢ ▷^n [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2.
  Proof.
    rewrite !big_sepL2_alt laterN_and big_sepL_laterN_2.
    auto using and_mono, laterN_intro.
  Qed.

  Lemma big_sepL2_flip Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l2; l1, Φ k y2 y1) ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1; l2, Φ k y1 y2).
  Proof.
    revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2]//=; simplify_eq.
    by rewrite IH.
  Qed.

  Global Instance big_sepL2_nil_persistent Φ :
    Persistent ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL2_persistent Φ l1 l2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    Persistent ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. rewrite big_sepL2_alt. apply _. Qed.

  Global Instance big_sepL2_nil_affine Φ :
    Affine ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL2_affine Φ l1 l2 :
    (∀ k x1 x2, Affine (Φ k x1 x2)) →
    Affine ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. rewrite big_sepL2_alt. apply _. Qed.

  Global Instance big_sepL2_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL2_timeless `{!Timeless (emp%I : PROP)} Φ l1 l2 :
    (∀ k x1 x2, Timeless (Φ k x1 x2)) →
    Timeless ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. rewrite big_sepL2_alt. apply _. Qed.
End sep_list2.

Lemma big_sepL2_ne_2 {A B : ofeT}
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

Section and_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_andL_nil Φ : ([∧ list] k↦y ∈ nil, Φ k y) ⊣⊢ True.
  Proof. done. Qed.
  Lemma big_andL_nil' P Φ : P ⊢ [∧ list] k↦y ∈ nil, Φ k y.
  Proof. by apply pure_intro. Qed.
  Lemma big_andL_cons Φ x l :
    ([∧ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∧ [∧ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_andL_singleton Φ x : ([∧ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_andL_app Φ l1 l2 :
    ([∧ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∧ list] k↦y ∈ l1, Φ k y) ∧ ([∧ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.

  Lemma big_andL_submseteq (Φ : A → PROP) l1 l2 :
    l1 ⊆+ l2 → ([∧ list] y ∈ l2, Φ y) ⊢ [∧ list] y ∈ l1, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. by rewrite big_andL_app and_elim_l.
  Qed.

  (** The lemmas [big_andL_mono], [big_andL_ne] and [big_andL_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_andL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y) ⊢ [∧ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_andL_ne Φ Ψ l n :
    (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y)%I ≡{n}≡ ([∧ list] k ↦ y ∈ l, Ψ k y)%I.
  Proof. apply big_opL_ne. Qed.
  Lemma big_andL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∧ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opL] instances. *)
  Global Instance big_andL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_and PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_andL_mono; intros; apply Hf. Qed.
  Global Instance big_andL_id_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_and PROP) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Lemma big_andL_lookup Φ l i x :
    l !! i = Some x → ([∧ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // big_andL_app /=.
    rewrite Nat.add_0_r take_length_le;
      eauto using lookup_lt_Some, Nat.lt_le_incl, and_elim_l', and_elim_r'.
  Qed.

  Lemma big_andL_elem_of (Φ : A → PROP) l x :
    x ∈ l → ([∧ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup. by eapply (big_andL_lookup (λ _, Φ)).
  Qed.

  Lemma big_andL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∧ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∧ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_andL_bind {B} (f : A → list B) (Φ : B → PROP) l :
    ([∧ list] y ∈ l ≫= f, Φ y) ⊣⊢ ([∧ list] x ∈ l, [∧ list] y ∈ f x, Φ y).
  Proof. by rewrite big_opL_bind. Qed.

  Lemma big_andL_and Φ Ψ l :
    ([∧ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊣⊢ ([∧ list] k↦x ∈ l, Φ k x) ∧ ([∧ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_op. Qed.

  Lemma big_andL_persistently Φ l :
    <pers> ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ [∧ list] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_andL_forall Φ l :
    ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_andL_lookup. }
    revert Φ. induction l as [|x l IH]=> Φ; [by auto using big_andL_nil'|].
    rewrite big_andL_cons. apply and_intro.
    - by rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
    - rewrite -IH. apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Global Instance big_andL_nil_persistent Φ :
    Persistent ([∧ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_andL_persistent Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∧ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
End and_list.

Section or_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_orL_nil Φ : ([∨ list] k↦y ∈ nil, Φ k y) ⊣⊢ False.
  Proof. done. Qed.
  Lemma big_orL_cons Φ x l :
    ([∨ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∨ [∨ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_orL_singleton Φ x : ([∨ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_orL_app Φ l1 l2 :
    ([∨ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∨ list] k↦y ∈ l1, Φ k y) ∨ ([∨ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.

  Lemma big_orL_submseteq (Φ : A → PROP) l1 l2 :
    l1 ⊆+ l2 → ([∨ list] y ∈ l1, Φ y) ⊢ [∨ list] y ∈ l2, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. by rewrite big_orL_app -or_intro_l.
  Qed.

  (** The lemmas [big_orL_mono], [big_orL_ne] and [big_orL_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_orL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∨ list] k ↦ y ∈ l, Φ k y) ⊢ [∨ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_orL_ne Φ Ψ l n :
    (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
    ([∨ list] k ↦ y ∈ l, Φ k y)%I ≡{n}≡ ([∨ list] k ↦ y ∈ l, Ψ k y)%I.
  Proof. apply big_opL_ne. Qed.
  Lemma big_orL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∨ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∨ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opL] instances. *)
  Global Instance big_orL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_or PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_orL_mono; intros; apply Hf. Qed.
  Global Instance big_orL_id_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_or PROP) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Lemma big_orL_lookup Φ l i x :
    l !! i = Some x → Φ i x ⊢ ([∨ list] k↦y ∈ l, Φ k y).
  Proof.
    intros. rewrite -(take_drop_middle l i x) // big_orL_app /=.
    rewrite Nat.add_0_r take_length_le;
      eauto using lookup_lt_Some, Nat.lt_le_incl, or_intro_l', or_intro_r'.
  Qed.

  Lemma big_orL_elem_of (Φ : A → PROP) l x :
    x ∈ l → Φ x ⊢ ([∨ list] y ∈ l, Φ y).
  Proof.
    intros [i ?]%elem_of_list_lookup; by eapply (big_orL_lookup (λ _, Φ)).
  Qed.

  Lemma big_orL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∨ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∨ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_orL_bind {B} (f : A → list B) (Φ : B → PROP) l :
    ([∨ list] y ∈ l ≫= f, Φ y) ⊣⊢ ([∨ list] x ∈ l, [∨ list] y ∈ f x, Φ y).
  Proof. by rewrite big_opL_bind. Qed.

  Lemma big_orL_or Φ Ψ l :
    ([∨ list] k↦x ∈ l, Φ k x ∨ Ψ k x)
    ⊣⊢ ([∨ list] k↦x ∈ l, Φ k x) ∨ ([∨ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_op. Qed.

  Lemma big_orL_persistently Φ l :
    <pers> ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ [∨ list] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_orL_exist Φ l :
    ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ (∃ k x, ⌜l !! k = Some x⌝ ∧ Φ k x).
  Proof.
    apply (anti_symm _).
    { revert Φ. induction l as [|x l IH]=> Φ.
      { rewrite big_orL_nil. apply False_elim. }
      rewrite big_orL_cons. apply or_elim.
      - by rewrite -(exist_intro 0) -(exist_intro x) pure_True // left_id.
      - rewrite IH. apply exist_elim=> k. by rewrite -(exist_intro (S k)). }
    apply exist_elim=> k; apply exist_elim=> x. apply pure_elim_l=> ?.
    by apply: big_orL_lookup.
  Qed.

  Lemma big_orL_sep_l P Φ l :
    P ∗ ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∨ list] k↦x ∈ l, P ∗ Φ k x).
  Proof.
    rewrite !big_orL_exist sep_exist_l.
    f_equiv=> k. rewrite sep_exist_l. f_equiv=> x.
    by rewrite !persistent_and_affinely_sep_l !assoc (comm _ P).
 Qed.
  Lemma big_orL_sep_r Q Φ l :
    ([∨ list] k↦x ∈ l, Φ k x) ∗ Q ⊣⊢ ([∨ list] k↦x ∈ l, Φ k x ∗ Q).
  Proof. setoid_rewrite (comm bi_sep). apply big_orL_sep_l. Qed.

  Global Instance big_orL_nil_persistent Φ :
    Persistent ([∨ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_orL_persistent Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∨ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
End or_list.

(** ** Big ops over finite maps *)
Section map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_subseteq `{BiAffine PROP} Φ m1 m2 :
    m2 ⊆ m1 → ([∗ map] k ↦ x ∈ m1, Φ k x) ⊢ [∗ map] k ↦ x ∈ m2, Φ k x.
  Proof. rewrite big_opM_eq. intros. by apply big_sepL_submseteq, map_to_list_submseteq. Qed.

  (** The lemmas [big_sepM_mono], [big_sepM_ne] and [big_sepM_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_sepM_mono Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof. apply big_opM_gen_proper; apply _ || auto. Qed.
  Lemma big_sepM_ne Φ Ψ m n :
    (∀ k x, m !! k = Some x → Φ k x ≡{n}≡ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x)%I ≡{n}≡ ([∗ map] k ↦ x ∈ m, Ψ k x)%I.
  Proof. apply big_opM_ne. Qed.
  Lemma big_sepM_proper Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗ map] k ↦ x ∈ m, Ψ k x).
  Proof. apply big_opM_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opM] instances. *)
  Global Instance big_sepM_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opM (@bi_sep PROP) (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_sepM_mono; intros; apply Hf. Qed.

  Lemma big_sepM_empty Φ : ([∗ map] k↦x ∈ ∅, Φ k x) ⊣⊢ emp.
  Proof. by rewrite big_opM_empty. Qed.
  Lemma big_sepM_empty' P `{!Affine P} Φ : P ⊢ [∗ map] k↦x ∈ ∅, Φ k x.
  Proof. rewrite big_sepM_empty. apply: affine. Qed.

  Lemma big_sepM_insert Φ m i x :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y.
  Proof. apply big_opM_insert. Qed.

  Lemma big_sepM_delete Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_delete. Qed.

  Lemma big_sepM_insert_delete Φ m i x :
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_insert_delete. Qed.

  Lemma big_sepM_insert_2 Φ m i x :
    TCOr (∀ x, Affine (Φ i x)) (Absorbing (Φ i x)) →
    Φ i x -∗ ([∗ map] k↦y ∈ m, Φ k y) -∗ [∗ map] k↦y ∈ <[i:=x]> m, Φ k y.
  Proof.
    intros Ha. apply wand_intro_r. destruct (m !! i) as [y|] eqn:Hi; last first.
    { by rewrite -big_sepM_insert. }
    assert (TCOr (Affine (Φ i y)) (Absorbing (Φ i x))).
    { destruct Ha; try apply _. }
    rewrite big_sepM_delete // assoc.
    rewrite (sep_elim_l (Φ i x)) -big_sepM_insert ?lookup_delete //.
    by rewrite insert_delete.
  Qed.

  Lemma big_sepM_lookup_acc Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ map] k↦y ∈ m, Φ k y)).
  Proof.
    intros. rewrite big_sepM_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepM_lookup Φ m i x `{!Absorbing (Φ i x)} :
    m !! i = Some x → ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
  Proof. intros. rewrite big_sepM_lookup_acc //. by rewrite sep_elim_l. Qed.

  Lemma big_sepM_lookup_dom (Φ : K → PROP) m i `{!Absorbing (Φ i)} :
    is_Some (m !! i) → ([∗ map] k↦_ ∈ m, Φ k) ⊢ Φ i.
  Proof. intros [x ?]. by eapply (big_sepM_lookup (λ i x, Φ i)). Qed.

  Lemma big_sepM_singleton Φ i x : ([∗ map] k↦y ∈ {[i:=x]}, Φ k y) ⊣⊢ Φ i x.
  Proof. by rewrite big_opM_singleton. Qed.

  Lemma big_sepM_fmap {B} (f : A → B) (Φ : K → B → PROP) m :
    ([∗ map] k↦y ∈ f <$> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k (f y)).
  Proof. by rewrite big_opM_fmap. Qed.

  Lemma big_sepM_omap {B} (f : A → option B) (Φ : K → B → PROP) m :
    ([∗ map] k↦y ∈ omap f m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, from_option (Φ k) emp (f y)).
  Proof. by rewrite big_opM_omap. Qed.

  Lemma big_sepM_insert_override Φ m i x x' :
    m !! i = Some x → (Φ i x ⊣⊢ Φ i x') →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k y).
  Proof. apply big_opM_insert_override. Qed.

  Lemma big_sepM_insert_override_1 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊢
      (Φ i x' -∗ Φ i x) -∗ ([∗ map] k↦y ∈ m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    by rewrite assoc wand_elim_l -big_sepM_delete.
  Qed.

  Lemma big_sepM_insert_override_2 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
      (Φ i x -∗ Φ i x') -∗ ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite {1}big_sepM_delete //; rewrite assoc wand_elim_l.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //.
  Qed.

  Lemma big_sepM_insert_acc Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
      Φ i x ∗ (∀ x', Φ i x' -∗ ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y)).
  Proof.
    intros ?. rewrite {1}big_sepM_delete //. apply sep_mono; [done|].
    apply forall_intro=> x'.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    by apply wand_intro_l.
  Qed.

  Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → PROP) (f : K → B) m i x b :
    m !! i = None →
       ([∗ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
    ⊣⊢ (Ψ i x b ∗ [∗ map] k↦y ∈ m, Ψ k y (f k)).
  Proof. apply big_opM_fn_insert. Qed.

  Lemma big_sepM_fn_insert' (Φ : K → PROP) m i x P :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∗ [∗ map] k↦y ∈ m, Φ k).
  Proof. apply big_opM_fn_insert'. Qed.

  Lemma big_sepM_union Φ m1 m2 :
    m1 ##ₘ m2 →
    ([∗ map] k↦y ∈ m1 ∪ m2, Φ k y)
    ⊣⊢ ([∗ map] k↦y ∈ m1, Φ k y) ∗ ([∗ map] k↦y ∈ m2, Φ k y).
  Proof. apply big_opM_union. Qed.

  Lemma big_sepM_sep Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ map] k↦x ∈ m, Φ k x) ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. apply big_opM_op. Qed.

  Lemma big_sepM_and Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∧ Ψ k x)
    ⊢ ([∗ map] k↦x ∈ m, Φ k x) ∧ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. auto using and_intro, big_sepM_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepM_persistently `{BiAffine PROP} Φ m :
    (<pers> ([∗ map] k↦x ∈ m, Φ k x)) ⊣⊢ ([∗ map] k↦x ∈ m, <pers> (Φ k x)).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_intuitionistically_forall Φ m :
    □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x) ⊢ [∗ map] k↦x ∈ m, Φ k x.
  Proof.
    revert Φ. induction m as [|i x m ? IH] using map_ind=> Φ.
    { by rewrite (affine (□ _)%I) big_sepM_empty. }
    rewrite big_sepM_insert // intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim i) (forall_elim x) lookup_insert.
      by rewrite pure_True // True_impl intuitionistically_elim.
    - rewrite -IH. f_equiv. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_True // True_impl.
  Qed.

  Lemma big_sepM_forall `{BiAffine PROP} Φ m :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepM_lookup. }
    rewrite -big_sepM_intuitionistically_forall. setoid_rewrite pure_impl_forall.
    by rewrite intuitionistic_intuitionistically.
  Qed.

  Lemma big_sepM_impl Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ map] k↦x ∈ m, Ψ k x.
  Proof.
    apply wand_intro_l. rewrite big_sepM_intuitionistically_forall -big_sepM_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepM_dup P `{!Affine P} m :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ map] k↦x ∈ m, P.
  Proof.
    apply wand_intro_l. induction m as [|i x m ? IH] using map_ind.
    { apply: big_sepM_empty'. }
    rewrite !big_sepM_insert //.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepM_later `{BiAffine PROP} Φ m :
    ▷ ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷ Φ k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_sepM_later_2 Φ m :
    ([∗ map] k↦x ∈ m, ▷ Φ k x) ⊢ ▷ [∗ map] k↦x ∈ m, Φ k x.
  Proof. by rewrite big_opM_commute. Qed.

  Lemma big_sepM_laterN `{BiAffine PROP} Φ n m :
    ▷^n ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷^n Φ k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_sepM_laterN_2 Φ n m :
    ([∗ map] k↦x ∈ m, ▷^n Φ k x) ⊢ ▷^n [∗ map] k↦x ∈ m, Φ k x.
  Proof. by rewrite big_opM_commute. Qed.

  Global Instance big_sepM_empty_persistent Φ :
    Persistent ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_eq /big_opM_def map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_persistent Φ m :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ map] k↦x ∈ m, Φ k x).
  Proof. rewrite big_opM_eq. intros. apply big_sepL_persistent=> _ [??]; apply _. Qed.

  Global Instance big_sepM_empty_affine Φ :
    Affine ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_eq /big_opM_def map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_affine Φ m :
    (∀ k x, Affine (Φ k x)) → Affine ([∗ map] k↦x ∈ m, Φ k x).
  Proof. rewrite big_opM_eq. intros. apply big_sepL_affine=> _ [??]; apply _. Qed.

  Global Instance big_sepM_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_eq /big_opM_def map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_timeless `{!Timeless (emp%I : PROP)} Φ m :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∗ map] k↦x ∈ m, Φ k x).
  Proof. rewrite big_opM_eq. intros. apply big_sepL_timeless=> _ [??]; apply _. Qed.
End map.

(** ** Big ops over two maps *)
Section map2.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : K → A → B → PROP.

  Lemma big_sepM2_lookup_iff Φ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2) ⊢
    ⌜ ∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k) ⌝.
  Proof. by rewrite big_sepM2_eq /big_sepM2_def and_elim_l. Qed.

  Lemma big_sepM2_dom Φ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2) ⊢
    ⌜ dom (gset K) m1 = dom (gset K) m2 ⌝.
  Proof.
    rewrite big_sepM2_lookup_iff. apply pure_mono=>Hm.
    apply elem_of_equiv_L=> k. by rewrite !elem_of_dom.
  Qed.

  Lemma big_sepM2_flip Φ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m2; m1, Φ k y2 y1) ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2).
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def.
    apply and_proper; [apply pure_proper; naive_solver |].
    rewrite -map_zip_with_flip map_zip_with_map_zip big_sepM_fmap.
    apply big_sepM_proper. by intros k [b a].
  Qed.

  (** The lemmas [big_sepM2_mono], [big_sepM2_ne] and [big_sepM2_proper] are more
  generic than the instances as they also give [mi !! k = Some yi] in the premise. *)
  Lemma big_sepM2_mono Φ Ψ m1 m2 :
    (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → Φ k y1 y2 ⊢ Ψ k y1 y2) →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ [∗ map] k ↦ y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    intros Hm1m2. rewrite big_sepM2_eq /big_sepM2_def.
    apply and_mono_r, big_sepM_mono.
    intros k [x1 x2]. rewrite map_lookup_zip_with.
    specialize (Hm1m2 k x1 x2).
    destruct (m1 !! k) as [y1|]; last done.
    destruct (m2 !! k) as [y2|]; simpl; last done.
    intros ?; simplify_eq. by apply Hm1m2.
  Qed.
  Lemma big_sepM2_ne Φ Ψ m1 m2 n :
    (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → Φ k y1 y2 ≡{n}≡ Ψ k y1 y2) →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2)%I ≡{n}≡ ([∗ map] k ↦ y1;y2 ∈ m1;m2, Ψ k y1 y2)%I.
  Proof.
    intros Hm1m2. rewrite big_sepM2_eq /big_sepM2_def.
    f_equiv. apply big_sepM_ne=> k [x1 x2]. rewrite map_lookup_zip_with.
    specialize (Hm1m2 k x1 x2).
    destruct (m1 !! k) as [y1|]; last done.
    destruct (m2 !! k) as [y2|]; simpl; last done.
    intros ?; simplify_eq. by apply Hm1m2.
  Qed.
  Lemma big_sepM2_proper Φ Ψ m1 m2 :
    (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → Φ k y1 y2 ⊣⊢ Ψ k y1 y2) →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢ [∗ map] k ↦ y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    intros; apply (anti_symm _);
      apply big_sepM2_mono; auto using equiv_entails, equiv_entails_sym.
  Qed.
  Lemma big_sepM2_proper_2 `{!Equiv A, !Equiv B} Φ Ψ m1 m2 m1' m2' :
    m1 ≡ m1' → m2 ≡ m2' →
    (∀ k y1 y1' y2 y2',
      m1 !! k = Some y1 → m1' !! k = Some y1' → y1 ≡ y1' →
      m2 !! k = Some y2 → m2' !! k = Some y2' → y2 ≡ y2' →
      Φ k y1 y2 ⊣⊢ Ψ k y1' y2') →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢ [∗ map] k ↦ y1;y2 ∈ m1';m2', Ψ k y1 y2.
  Proof.
    intros Hm1 Hm2 Hf. rewrite big_sepM2_eq /big_sepM2_def. f_equiv.
    { f_equiv; split; intros Hm k.
      - trans (is_Some (m1 !! k)); [symmetry; apply is_Some_proper; by f_equiv|].
        rewrite Hm. apply is_Some_proper; by f_equiv.
      - trans (is_Some (m1' !! k)); [apply is_Some_proper; by f_equiv|].
        rewrite Hm. symmetry. apply is_Some_proper; by f_equiv. }
    apply big_opM_proper_2; [by f_equiv|].
    intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some
      (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some [??]; naive_solver.
  Qed.

  Global Instance big_sepM2_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n)))
      ==> (=) ==> (=) ==> (dist n))
           (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B)).
  Proof. intros f g Hf m1 ? <- m2 ? <-. apply big_sepM2_ne; intros; apply Hf. Qed.
  Global Instance big_sepM2_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
      ==> (=) ==> (=) ==> (⊢)) (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B)).
  Proof. intros f g Hf m1 ? <- m2 ? <-. apply big_sepM2_mono; intros; apply Hf. Qed.
  Global Instance big_sepM2_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊣⊢)))
      ==> (=) ==> (=) ==> (⊣⊢)) (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B)).
  Proof. intros f g Hf m1 ? <- m2 ? <-. apply big_sepM2_proper; intros; apply Hf. Qed.

  Lemma big_sepM2_empty Φ : ([∗ map] k↦y1;y2 ∈ ∅; ∅, Φ k y1 y2) ⊣⊢ emp.
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def big_opM_eq pure_True ?left_id //.
    intros k. rewrite !lookup_empty; split; by inversion 1.
  Qed.
  Lemma big_sepM2_empty' P `{!Affine P} Φ : P ⊢ [∗ map] k↦y1;y2 ∈ ∅;∅, Φ k y1 y2.
  Proof. rewrite big_sepM2_empty. apply: affine. Qed.

  Lemma big_sepM2_empty_l m1 Φ : ([∗ map] k↦y1;y2 ∈ m1; ∅, Φ k y1 y2) ⊢ ⌜m1 = ∅⌝.
  Proof.
    rewrite big_sepM2_dom dom_empty_L.
    apply pure_mono, dom_empty_inv_L.
  Qed.

  Lemma big_sepM2_empty_r m2 Φ : ([∗ map] k↦y1;y2 ∈ ∅; m2, Φ k y1 y2) ⊢ ⌜m2 = ∅⌝.
  Proof.
    rewrite big_sepM2_dom dom_empty_L.
    apply pure_mono=>?. eapply (dom_empty_inv_L (D:=gset K)). eauto.
  Qed.

  Lemma big_sepM2_insert Φ m1 m2 i x1 x2 :
    m1 !! i = None → m2 !! i = None →
    ([∗ map] k↦y1;y2 ∈ <[i:=x1]>m1; <[i:=x2]>m2, Φ k y1 y2)
    ⊣⊢ Φ i x1 x2 ∗ [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2.
  Proof.
    intros Hm1 Hm2. rewrite big_sepM2_eq /big_sepM2_def -map_insert_zip_with.
    rewrite big_sepM_insert;
      last by rewrite map_lookup_zip_with Hm1.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite sep_assoc (sep_comm _ (Φ _ _ _)) -sep_assoc.
    repeat apply sep_proper=>//.
    apply affinely_proper, pure_proper.
    split.
    - intros H1 k. destruct (decide (i = k)) as [->|?].
      + rewrite Hm1 Hm2 //. by split; intros ?; exfalso; eapply is_Some_None.
      + specialize (H1 k). revert H1. rewrite !lookup_insert_ne //.
    - intros H1 k. destruct (decide (i = k)) as [->|?].
      + rewrite !lookup_insert. split; by econstructor.
      + rewrite !lookup_insert_ne //.
  Qed.

  Lemma big_sepM2_delete Φ m1 m2 i x1 x2 :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) ⊣⊢
      Φ i x1 x2 ∗ [∗ map] k↦x;y ∈ delete i m1;delete i m2, Φ k x y.
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def => Hx1 Hx2.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite sep_assoc (sep_comm  (Φ _ _ _)) -sep_assoc.
    apply sep_proper.
    - apply affinely_proper, pure_proper. split.
      + intros Hm k. destruct (decide (i = k)) as [->|?].
        { rewrite !lookup_delete. split; intros []%is_Some_None. }
        rewrite !lookup_delete_ne //.
      + intros Hm k. specialize (Hm k). revert Hm. destruct (decide (i = k)) as [->|?].
        { intros _. rewrite Hx1 Hx2. split; eauto. }
        rewrite !lookup_delete_ne //.
    - rewrite -map_delete_zip_with.
      apply (big_sepM_delete (λ i xx, Φ i xx.1 xx.2) (map_zip m1 m2) i (x1,x2)).
      by rewrite map_lookup_zip_with Hx1 Hx2.
  Qed.

  Lemma big_sepM2_insert_delete Φ m1 m2 i x1 x2 :
    ([∗ map] k↦y1;y2 ∈ <[i:=x1]>m1; <[i:=x2]>m2, Φ k y1 y2)
    ⊣⊢ Φ i x1 x2 ∗ [∗ map] k↦y1;y2 ∈ delete i m1;delete i m2, Φ k y1 y2.
  Proof.
    rewrite -(insert_delete m1) -(insert_delete m2).
    apply big_sepM2_insert; by rewrite lookup_delete.
  Qed.

  Lemma big_sepM2_insert_acc Φ m1 m2 i x1 x2 :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (∀ x1' x2', Φ i x1' x2' -∗
        ([∗ map] k↦y1;y2 ∈ <[i:=x1']>m1;<[i:=x2']>m2, Φ k y1 y2)).
  Proof.
    intros ??. rewrite {1}big_sepM2_delete //. apply sep_mono; [done|].
    apply forall_intro=> x1'. apply forall_intro=> x2'.
    rewrite -(insert_delete m1) -(insert_delete m2) big_sepM2_insert ?lookup_delete //.
    by apply wand_intro_l.
  Qed.

  Lemma big_sepM2_insert_2 Φ m1 m2 i x1 x2 :
    TCOr (∀ x y, Affine (Φ i x y)) (Absorbing (Φ i x1 x2)) →
    Φ i x1 x2 -∗
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    ([∗ map] k↦y1;y2 ∈ <[i:=x1]>m1; <[i:=x2]>m2, Φ k y1 y2).
  Proof.
    intros Ha. rewrite big_sepM2_eq /big_sepM2_def.
    assert (TCOr (∀ x, Affine (Φ i x.1 x.2)) (Absorbing (Φ i x1 x2))).
    { destruct Ha; try apply _. }
    apply wand_intro_r.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite (sep_comm  (Φ _ _ _)) -sep_assoc. apply sep_mono.
    { apply affinely_mono, pure_mono. intros Hm k.
      rewrite !lookup_insert_is_Some. naive_solver. }
    rewrite (big_sepM_insert_2 (λ k xx, Φ k xx.1 xx.2) (map_zip m1 m2) i (x1, x2)).
    rewrite map_insert_zip_with. apply wand_elim_r.
  Qed.

  Lemma big_sepM2_lookup_acc Φ m1 m2 i x1 x2 :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (Φ i x1 x2 -∗ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)).
  Proof.
    intros Hm1 Hm2. etrans; first apply big_sepM2_insert_acc=>//.
    apply sep_mono_r. rewrite (forall_elim x1) (forall_elim x2).
    rewrite !insert_id //.
 Qed.

  Lemma big_sepM2_lookup Φ m1 m2 i x1 x2 `{!Absorbing (Φ i x1 x2)} :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ Φ i x1 x2.
  Proof. intros. rewrite big_sepM2_lookup_acc //. by rewrite sep_elim_l. Qed.

  Lemma big_sepM2_lookup_1 Φ m1 m2 i x1 `{!∀ x2, Absorbing (Φ i x1 x2)} :
    m1 !! i = Some x1 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊢ ∃ x2, ⌜m2 !! i = Some x2⌝ ∧ Φ i x1 x2.
  Proof.
    intros Hm1. rewrite big_sepM2_eq /big_sepM2_def.
    rewrite persistent_and_sep_1.
    apply wand_elim_l'. apply pure_elim'=>Hm.
    assert (is_Some (m2 !! i)) as [x2 Hm2].
    { apply Hm. by econstructor. }
    apply wand_intro_r. rewrite -(exist_intro x2).
    rewrite /big_sepM2 (big_sepM_lookup _ _ i (x1,x2));
      last by rewrite map_lookup_zip_with Hm1 Hm2.
    rewrite pure_True// sep_elim_r.
    apply and_intro=>//. by apply pure_intro.
  Qed.

  Lemma big_sepM2_lookup_2 Φ m1 m2 i x2 `{!∀ x1, Absorbing (Φ i x1 x2)} :
    m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊢ ∃ x1, ⌜m1 !! i = Some x1⌝ ∧ Φ i x1 x2.
  Proof.
    intros Hm2. rewrite big_sepM2_eq /big_sepM2_def.
    rewrite persistent_and_sep_1.
    apply wand_elim_l'. apply pure_elim'=>Hm.
    assert (is_Some (m1 !! i)) as [x1 Hm1].
    { apply Hm. by econstructor. }
    apply wand_intro_r. rewrite -(exist_intro x1).
    rewrite /big_sepM2 (big_sepM_lookup _ _ i (x1,x2));
      last by rewrite map_lookup_zip_with Hm1 Hm2.
    rewrite pure_True// sep_elim_r.
    apply and_intro=>//. by apply pure_intro.
  Qed.

  Lemma big_sepM2_singleton Φ i x1 x2 :
    ([∗ map] k↦y1;y2 ∈ {[ i := x1 ]}; {[ i := x2 ]}, Φ k y1 y2) ⊣⊢ Φ i x1 x2.
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def.
    rewrite map_zip_with_singleton big_sepM_singleton.
    apply (anti_symm _).
    - apply and_elim_r.
    - rewrite <- (left_id True%I (∧)%I (Φ i x1 x2)).
      apply and_mono=>//. apply pure_mono=>_ k.
      rewrite !lookup_insert_is_Some' !lookup_empty -!not_eq_None_Some.
      naive_solver.
  Qed.

  Lemma big_sepM2_fmap {A' B'} (f : A → A') (g : B → B') (Φ : K → A' → B' → PROP) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ f <$> m1; g <$> m2, Φ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k (f y1) (g y2)).
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def. rewrite map_fmap_zip.
    apply and_proper.
    - setoid_rewrite lookup_fmap. by setoid_rewrite fmap_is_Some.
    - by rewrite big_sepM_fmap.
  Qed.

  Lemma big_sepM2_fmap_l {A'} (f : A → A') (Φ : K → A' → B → PROP) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ f <$> m1; m2, Φ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k (f y1) y2).
  Proof. rewrite -{1}(map_fmap_id m2). apply big_sepM2_fmap. Qed.

  Lemma big_sepM2_fmap_r {B'} (g : B → B') (Φ : K → A → B' → PROP) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1; g <$> m2, Φ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 (g y2)).
  Proof. rewrite -{1}(map_fmap_id m1). apply big_sepM2_fmap. Qed.

  Lemma big_sepM2_sep Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∗ Ψ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ∗ ([∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2).
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def.
    rewrite -{1}(and_idem ⌜∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)⌝%I).
    rewrite -and_assoc.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite -sep_assoc. apply sep_proper=>//.
    rewrite sep_assoc (sep_comm _ (<affine> _)%I) -sep_assoc.
    apply sep_proper=>//. apply big_sepM_sep.
  Qed.

  Lemma big_sepM2_and Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∧ Ψ k y1 y2)
    ⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ∧ ([∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2).
  Proof. auto using and_intro, big_sepM2_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepM2_persistently `{BiAffine PROP} Φ m1 m2 :
    <pers> ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊣⊢ [∗ map] k↦y1;y2 ∈ m1;m2, <pers> (Φ k y1 y2).
  Proof.
    by rewrite big_sepM2_eq /big_sepM2_def persistently_and
         persistently_pure big_sepM_persistently.
  Qed.

  Lemma big_sepM2_intuitionistically_forall Φ m1 m2 :
    (∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
    □ (∀ k x1 x2, ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ → Φ k x1 x2) ⊢
    [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2.
  Proof.
    intros. rewrite big_sepM2_eq /big_sepM2_def.
    apply and_intro; [by apply pure_intro|].
    rewrite -big_sepM_intuitionistically_forall. f_equiv; f_equiv=> k.
    apply forall_intro=> -[x1 x2]. rewrite (forall_elim x1) (forall_elim x2).
    apply impl_intro_l, pure_elim_l.
    intros (?&?&[= <- <-]&?&?)%map_lookup_zip_with_Some.
    by rewrite !pure_True // !True_impl.
  Qed.

  Lemma big_sepM2_forall `{BiAffine PROP} Φ m1 m2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢
      ⌜∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)⌝
      ∧ (∀ k x1 x2, ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ → Φ k x1 x2).
  Proof.
    intros. apply (anti_symm _).
    - apply and_intro; [apply big_sepM2_lookup_iff|].
      apply forall_intro=> k. apply forall_intro=> x1. apply forall_intro=> x2.
      do 2 (apply impl_intro_l; apply pure_elim_l=> ?). by apply :big_sepM2_lookup.
    - apply pure_elim_l=> ?. rewrite -big_sepM2_intuitionistically_forall //.
      repeat setoid_rewrite pure_impl_forall.
      by rewrite intuitionistic_intuitionistically.
  Qed.

  Lemma big_sepM2_impl Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    □ (∀ k x1 x2,
      ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    rewrite -(idemp bi_and (big_sepM2 _ _ _)) {1}big_sepM2_lookup_iff.
    apply pure_elim_l=> ?. rewrite big_sepM2_intuitionistically_forall //.
    apply bi.wand_intro_l. rewrite -big_sepM2_sep. by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepM2_later_1 `{BiAffine PROP} Φ m1 m2 :
    (▷ [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2)
    ⊢ ◇ ([∗ map] k↦x1;x2 ∈ m1;m2, ▷ Φ k x1 x2).
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def later_and (timeless ⌜_⌝%I).
    rewrite big_sepM_later except_0_and.
    auto using and_mono_r, except_0_intro.
  Qed.
  Lemma big_sepM2_later_2 Φ m1 m2 :
    ([∗ map] k↦x1;x2 ∈ m1;m2, ▷ Φ k x1 x2)
    ⊢ ▷ [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2.
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def later_and -(later_intro ⌜_⌝%I).
    apply and_mono_r. by rewrite big_opM_commute.
  Qed.

  Lemma big_sepM2_laterN_2 Φ n m1 m2 :
    ([∗ map] k↦x1;x2 ∈ m1;m2, ▷^n Φ k x1 x2)
    ⊢ ▷^n [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2.
  Proof.
    induction n as [|n IHn]; first done.
    rewrite later_laterN -IHn -big_sepM2_later_2.
    apply big_sepM2_mono. eauto.
  Qed.

  Global Instance big_sepM2_empty_persistent Φ :
    Persistent ([∗ map] k↦y1;y2 ∈ ∅; ∅, Φ k y1 y2).
  Proof. rewrite big_sepM2_empty. apply _. Qed.
  Global Instance big_sepM2_persistent Φ m1 m2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    Persistent ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
  Proof. rewrite big_sepM2_eq /big_sepM2_def. apply _. Qed.

  Global Instance big_sepM2_empty_affine Φ :
    Affine ([∗ map] k↦y1;y2 ∈ ∅; ∅, Φ k y1 y2).
  Proof. rewrite big_sepM2_empty. apply _. Qed.
  Global Instance big_sepM2_affine Φ m1 m2 :
    (∀ k x1 x2, Affine (Φ k x1 x2)) →
    Affine ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
  Proof. rewrite big_sepM2_eq /big_sepM2_def. apply _. Qed.

  Global Instance big_sepM2_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ map] k↦x1;x2 ∈ ∅;∅, Φ k x1 x2).
  Proof. rewrite big_sepM2_eq /big_sepM2_def map_zip_with_empty. apply _. Qed.
  Global Instance big_sepM2_timeless `{!Timeless (emp%I : PROP)} Φ m1 m2 :
    (∀ k x1 x2, Timeless (Φ k x1 x2)) →
    Timeless ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2).
  Proof. intros. rewrite big_sepM2_eq /big_sepM2_def. apply _. Qed.
End map2.

Lemma big_sepM2_ne_2 `{Countable K} (A B : ofeT)
    (Φ Ψ : K → A → B → PROP) m1 m2 m1' m2' n :
  m1 ≡{n}≡ m1' → m2 ≡{n}≡ m2' →
  (∀ k y1 y1' y2 y2',
    m1 !! k = Some y1 → m1' !! k = Some y1' → y1 ≡{n}≡ y1' →
    m2 !! k = Some y2 → m2' !! k = Some y2' → y2 ≡{n}≡ y2' →
    Φ k y1 y2 ≡{n}≡ Ψ k y1' y2') →
  ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2)%I ≡{n}≡ ([∗ map] k ↦ y1;y2 ∈ m1';m2', Ψ k y1 y2)%I.
Proof.
  intros Hm1 Hm2 Hf. rewrite big_sepM2_eq /big_sepM2_def. f_equiv.
  { f_equiv; split; intros Hm k.
    - trans (is_Some (m1 !! k)); [symmetry; apply: is_Some_ne; by f_equiv|].
      rewrite Hm. apply: is_Some_ne; by f_equiv.
    - trans (is_Some (m1' !! k)); [apply: is_Some_ne; by f_equiv|].
      rewrite Hm. symmetry. apply: is_Some_ne; by f_equiv. }
  apply big_opM_ne_2; [by f_equiv|].
  intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some
    (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some [??]; naive_solver.
Qed.

(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types Φ : A → PROP.

  Lemma big_sepS_subseteq `{BiAffine PROP} Φ X Y :
    Y ⊆ X → ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ Y, Φ x.
  Proof. rewrite big_opS_eq. intros. by apply big_sepL_submseteq, elements_submseteq. Qed.

  (** The lemmas [big_sepS_mono], [big_sepS_ne] and [big_sepS_proper] are more
  generic than the instances as they also give [x ∈ X] in the premise. *)
  Lemma big_sepS_mono Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ X, Ψ x.
  Proof. intros. apply big_opS_gen_proper; apply _ || auto. Qed.
  Lemma big_sepS_ne Φ Ψ X n :
    (∀ x, x ∈ X → Φ x ≡{n}≡ Ψ x) →
    ([∗ set] x ∈ X, Φ x)%I ≡{n}≡ ([∗ set] x ∈ X, Ψ x)%I.
  Proof. apply big_opS_ne. Qed.
  Lemma big_sepS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ set] x ∈ X, Ψ x).
  Proof. apply big_opS_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opS] instances. *)
  Global Instance big_sepS_mono' :
     Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opS (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. by apply big_sepS_mono. Qed.

  Lemma big_sepS_empty Φ : ([∗ set] x ∈ ∅, Φ x) ⊣⊢ emp.
  Proof. by rewrite big_opS_empty. Qed.
  Lemma big_sepS_empty' P `{!Affine P} Φ : P ⊢ [∗ set] x ∈ ∅, Φ x.
  Proof. rewrite big_sepS_empty. apply: affine. Qed.

  Lemma big_sepS_insert Φ X x :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, Φ y) ⊣⊢ (Φ x ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_insert. Qed.

  Lemma big_sepS_fn_insert {B} (Ψ : A → B → PROP) f X x b :
    x ∉ X →
       ([∗ set] y ∈ {[ x ]} ∪ X, Ψ y (<[x:=b]> f y))
    ⊣⊢ (Ψ x b ∗ [∗ set] y ∈ X, Ψ y (f y)).
  Proof. apply big_opS_fn_insert. Qed.

  Lemma big_sepS_fn_insert' Φ X x P :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, <[x:=P]> Φ y) ⊣⊢ (P ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_fn_insert'. Qed.

  Lemma big_sepS_union Φ X Y :
    X ## Y →
    ([∗ set] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ Y, Φ y).
  Proof. apply big_opS_union. Qed.

  Lemma big_sepS_delete Φ X x :
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ set] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply big_opS_delete. Qed.

  Lemma big_sepS_elem_of Φ X x `{!Absorbing (Φ x)} :
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. rewrite big_sepS_delete //. by rewrite sep_elim_l. Qed.

  Lemma big_sepS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ set] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ set] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepS_singleton Φ x : ([∗ set] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opS_singleton. Qed.

  Lemma big_sepS_filter' (P : A → Prop) `{∀ x, Decision (P x)} Φ X :
    ([∗ set] y ∈ filter P X, Φ y)
    ⊣⊢ ([∗ set] y ∈ X, if decide (P y) then Φ y else emp).
  Proof.
    induction X as [|x X ? IH] using set_ind_L.
    { by rewrite filter_empty_L !big_sepS_empty. }
    destruct (decide (P x)).
    - rewrite filter_union_L filter_singleton_L //.
      rewrite !big_sepS_insert //; last set_solver.
      by rewrite decide_True // IH.
    - rewrite filter_union_L filter_singleton_not_L // left_id_L.
      by rewrite !big_sepS_insert // decide_False // IH left_id.
  Qed.

  Lemma big_sepS_filter_acc' (P : A → Prop) `{∀ y, Decision (P y)} Φ X Y :
    (∀ y, y ∈ Y → P y → y ∈ X) →
    ([∗ set] y ∈ X, Φ y) -∗
      ([∗ set] y ∈ Y, if decide (P y) then Φ y else emp) ∗
      (([∗ set] y ∈ Y, if decide (P y) then Φ y else emp) -∗ [∗ set] y ∈ X, Φ y).
  Proof.
    intros ?. destruct (proj1 (subseteq_disjoint_union_L (filter P Y) X))
      as (Z&->&?); first set_solver.
    rewrite big_sepS_union // big_sepS_filter'.
    by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepS_filter `{BiAffine PROP}
      (P : A → Prop) `{∀ x, Decision (P x)} Φ X :
    ([∗ set] y ∈ filter P X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ⌜P y⌝ → Φ y).
  Proof. setoid_rewrite <-decide_emp. apply big_sepS_filter'. Qed.

  Lemma big_sepS_filter_acc `{BiAffine PROP}
      (P : A → Prop) `{∀ y, Decision (P y)} Φ X Y :
    (∀ y, y ∈ Y → P y → y ∈ X) →
    ([∗ set] y ∈ X, Φ y) -∗
      ([∗ set] y ∈ Y, ⌜P y⌝ → Φ y) ∗
      (([∗ set] y ∈ Y, ⌜P y⌝ → Φ y) -∗ [∗ set] y ∈ X, Φ y).
  Proof. intros. setoid_rewrite <-decide_emp. by apply big_sepS_filter_acc'. Qed.

  Lemma big_sepS_list_to_set Φ (l : list A) :
    NoDup l →
    ([∗ set] x ∈ list_to_set l, Φ x) ⊣⊢ [∗ list] x ∈ l, Φ x.
  Proof. apply big_opS_list_to_set. Qed.

  Lemma big_sepS_sep Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ X, Ψ y).
  Proof. apply big_opS_op. Qed.

  Lemma big_sepS_and Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ set] y ∈ X, Φ y) ∧ ([∗ set] y ∈ X, Ψ y).
  Proof. auto using and_intro, big_sepS_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepS_persistently `{BiAffine PROP} Φ X :
    <pers> ([∗ set] y ∈ X, Φ y) ⊣⊢ [∗ set] y ∈ X, <pers> (Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_intuitionistically_forall Φ X :
    □ (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ [∗ set] x ∈ X, Φ x.
  Proof.
    revert Φ. induction X as [|x X ? IH] using set_ind_L=> Φ.
    { by rewrite (affine (□ _)%I) big_sepS_empty. }
    rewrite intuitionistically_sep_dup big_sepS_insert //. f_equiv.
    - rewrite (forall_elim x) pure_True ?True_impl; last set_solver.
      by rewrite intuitionistically_elim.
    - rewrite -IH. f_equiv. apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last set_solver.
  Qed.

  Lemma big_sepS_forall `{BiAffine PROP} Φ X :
    (∀ x, Persistent (Φ x)) → ([∗ set] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepS_elem_of. }
    rewrite -big_sepS_intuitionistically_forall. setoid_rewrite pure_impl_forall.
    by rewrite intuitionistic_intuitionistically.
  Qed.

  Lemma big_sepS_impl Φ Ψ X :
    ([∗ set] x ∈ X, Φ x) -∗
    □ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x) -∗
    [∗ set] x ∈ X, Ψ x.
  Proof.
    apply wand_intro_l. rewrite big_sepS_intuitionistically_forall -big_sepS_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepS_dup P `{!Affine P} X :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ set] x ∈ X, P.
  Proof.
    apply wand_intro_l. induction X as [|x X ? IH] using set_ind_L.
    { apply: big_sepS_empty'. }
    rewrite !big_sepS_insert //.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepS_later `{BiAffine PROP} Φ X :
    ▷ ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷ Φ y).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_sepS_later_2 Φ X :
    ([∗ set] y ∈ X, ▷ Φ y) ⊢ ▷ ([∗ set] y ∈ X, Φ y).
  Proof. by rewrite big_opS_commute. Qed.

  Lemma big_sepS_laterN `{BiAffine PROP} Φ n X :
    ▷^n ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_sepS_laterN_2 Φ n X :
    ([∗ set] y ∈ X, ▷^n Φ y) ⊢ ▷^n ([∗ set] y ∈ X, Φ y).
  Proof. by rewrite big_opS_commute. Qed.

  Global Instance big_sepS_empty_persistent Φ :
    Persistent ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite big_opS_eq /big_opS_def elements_empty. apply _. Qed.
  Global Instance big_sepS_persistent Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ set] x ∈ X, Φ x).
  Proof. rewrite big_opS_eq /big_opS_def. apply _. Qed.

  Global Instance big_sepS_empty_affine Φ : Affine ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite big_opS_eq /big_opS_def elements_empty. apply _. Qed.
  Global Instance big_sepS_affine Φ X :
    (∀ x, Affine (Φ x)) → Affine ([∗ set] x ∈ X, Φ x).
  Proof. rewrite big_opS_eq /big_opS_def. apply _. Qed.

  Global Instance big_sepS_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite big_opS_eq /big_opS_def elements_empty. apply _. Qed.
  Global Instance big_sepS_timeless `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ set] x ∈ X, Φ x).
  Proof. rewrite big_opS_eq /big_opS_def. apply _. Qed.
End gset.

Lemma big_sepM_dom `{Countable K} {A} (Φ : K → PROP) (m : gmap K A) :
  ([∗ map] k↦_ ∈ m, Φ k) ⊣⊢ ([∗ set] k ∈ dom _ m, Φ k).
Proof. apply big_opM_dom. Qed.

(** ** Big ops over finite multisets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types Φ : A → PROP.

  Lemma big_sepMS_subseteq `{BiAffine PROP} Φ X Y :
    Y ⊆ X → ([∗ mset] x ∈ X, Φ x) ⊢ [∗ mset] x ∈ Y, Φ x.
  Proof.
    intros. rewrite big_opMS_eq.
    by apply big_sepL_submseteq, gmultiset_elements_submseteq.
  Qed.

  (** The lemmas [big_sepMS_mono], [big_sepMS_ne] and [big_sepMS_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_sepMS_mono Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊢ [∗ mset] x ∈ X, Ψ x.
  Proof. intros. apply big_opMS_gen_proper; apply _ || auto. Qed.
  Lemma big_sepMS_ne Φ Ψ X n :
    (∀ x, x ∈ X → Φ x ≡{n}≡ Ψ x) →
    ([∗ mset] x ∈ X, Φ x)%I ≡{n}≡ ([∗ mset] x ∈ X, Ψ x)%I.
  Proof. apply big_opMS_ne. Qed.
  Lemma big_sepMS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊣⊢ ([∗ mset] x ∈ X, Ψ x).
  Proof. apply big_opMS_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opMS] instances. *)
  Global Instance big_sepMS_mono' :
     Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opMS (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. by apply big_sepMS_mono. Qed.

  Lemma big_sepMS_empty Φ : ([∗ mset] x ∈ ∅, Φ x) ⊣⊢ emp.
  Proof. by rewrite big_opMS_empty. Qed.
  Lemma big_sepMS_empty' P `{!Affine P} Φ : P ⊢ [∗ mset] x ∈ ∅, Φ x.
  Proof. rewrite big_sepMS_empty. apply: affine. Qed.

  Lemma big_sepMS_disj_union Φ X Y :
    ([∗ mset] y ∈ X ⊎ Y, Φ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ [∗ mset] y ∈ Y, Φ y.
  Proof. apply big_opMS_disj_union. Qed.

  Lemma big_sepMS_delete Φ X x :
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ mset] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply big_opMS_delete. Qed.

  Lemma big_sepMS_elem_of Φ X x `{!Absorbing (Φ x)} :
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. rewrite big_sepMS_delete //. by rewrite sep_elim_l. Qed.

  Lemma big_sepMS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ mset] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ mset] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepMS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepMS_singleton Φ x : ([∗ mset] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opMS_singleton. Qed.

  Lemma big_sepMS_sep Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ ([∗ mset] y ∈ X, Ψ y).
  Proof. apply big_opMS_op. Qed.

  Lemma big_sepMS_and Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ mset] y ∈ X, Φ y) ∧ ([∗ mset] y ∈ X, Ψ y).
  Proof. auto using and_intro, big_sepMS_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepMS_later `{BiAffine PROP} Φ X :
    ▷ ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷ Φ y).
  Proof. apply (big_opMS_commute _). Qed.
  Lemma big_sepMS_later_2 Φ X :
    ([∗ mset] y ∈ X, ▷ Φ y) ⊢ ▷ [∗ mset] y ∈ X, Φ y.
  Proof. by rewrite big_opMS_commute. Qed.

  Lemma big_sepMS_laterN `{BiAffine PROP} Φ n X :
    ▷^n ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opMS_commute _). Qed.
  Lemma big_sepMS_laterN_2 Φ n X :
    ([∗ mset] y ∈ X, ▷^n Φ y) ⊢ ▷^n [∗ mset] y ∈ X, Φ y.
  Proof. by rewrite big_opMS_commute. Qed.

  Lemma big_sepMS_persistently `{BiAffine PROP} Φ X :
    <pers> ([∗ mset] y ∈ X, Φ y) ⊣⊢ [∗ mset] y ∈ X, <pers> (Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Lemma big_sepMS_intuitionistically_forall Φ X :
    □ (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ [∗ mset] x ∈ X, Φ x.
  Proof.
    revert Φ. induction X as [|x X IH] using gmultiset_ind=> Φ.
    { by rewrite (affine (□ _)%I) big_sepMS_empty. }
    rewrite intuitionistically_sep_dup big_sepMS_disj_union.
    rewrite big_sepMS_singleton. f_equiv.
    - rewrite (forall_elim x) pure_True ?True_impl; last set_solver.
      by rewrite intuitionistically_elim.
    - rewrite -IH. f_equiv. apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last set_solver.
  Qed.

  Lemma big_sepMS_forall `{BiAffine PROP} Φ X :
    (∀ x, Persistent (Φ x)) → ([∗ mset] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepMS_elem_of. }
    rewrite -big_sepMS_intuitionistically_forall. setoid_rewrite pure_impl_forall.
    by rewrite intuitionistic_intuitionistically.
  Qed.

  Lemma big_sepMS_impl Φ Ψ X :
    ([∗ mset] x ∈ X, Φ x) -∗
    □ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x) -∗
    [∗ mset] x ∈ X, Ψ x.
  Proof.
    apply wand_intro_l. rewrite big_sepMS_intuitionistically_forall -big_sepMS_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepMS_dup P `{!Affine P} X :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ mset] x ∈ X, P.
  Proof.
    apply wand_intro_l. induction X as [|x X IH] using gmultiset_ind.
    { apply: big_sepMS_empty'. }
    rewrite !big_sepMS_disj_union big_sepMS_singleton.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Global Instance big_sepMS_empty_persistent Φ :
    Persistent ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite big_opMS_eq /big_opMS_def gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_persistent Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite big_opMS_eq /big_opMS_def. apply _. Qed.

  Global Instance big_sepMS_empty_affine Φ : Affine ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite big_opMS_eq /big_opMS_def gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_affine Φ X :
    (∀ x, Affine (Φ x)) → Affine ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite big_opMS_eq /big_opMS_def. apply _. Qed.

  Global Instance big_sepMS_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite big_opMS_eq /big_opMS_def gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_timeless `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite big_opMS_eq /big_opMS_def. apply _. Qed.
End gmultiset.
End big_op.
