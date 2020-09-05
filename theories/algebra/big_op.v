From stdpp Require Export functions gmap gmultiset.
From iris.algebra Require Export monoid.
From iris Require Import options.
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

(** We define the following big operators with binders build in:

- The operator [ [^o list] k ↦ x ∈ l, P ] folds over a list [l]. The binder [x]
  refers to each element at index [k].
- The operator [ [^o map] k ↦ x ∈ m, P ] folds over a map [m]. The binder [x]
  refers to each element at index [k].
- The operator [ [^o set] x ∈ X, P ] folds over a set [X]. The binder [x] refers
  to each element.

Since these big operators are like quantifiers, they have the same precedence as
[∀] and [∃]. *)

(** * Big ops over lists *)
Fixpoint big_opL `{Monoid M o} {A} (f : nat → A → M) (xs : list A) : M :=
  match xs with
  | [] => monoid_unit
  | x :: xs => o (f 0 x) (big_opL (λ n, f (S n)) xs)
  end.
Instance: Params (@big_opL) 4 := {}.
Arguments big_opL {M} o {_ A} _ !_ /.
Typeclasses Opaque big_opL.
Notation "'[^' o 'list]' k ↦ x ∈ l , P" := (big_opL o (λ k x, P) l)
  (at level 200, o at level 1, l at level 10, k, x at level 1, right associativity,
   format "[^ o  list]  k ↦ x  ∈  l ,  P") : stdpp_scope.
Notation "'[^' o 'list]' x ∈ l , P" := (big_opL o (λ _ x, P) l)
  (at level 200, o at level 1, l at level 10, x at level 1, right associativity,
   format "[^ o  list]  x  ∈  l ,  P") : stdpp_scope.

Definition big_opM_def `{Monoid M o} `{Countable K} {A} (f : K → A → M)
  (m : gmap K A) : M := big_opL o (λ _, curry f) (map_to_list m).
Definition big_opM_aux : seal (@big_opM_def). Proof. by eexists. Qed.
Definition big_opM := big_opM_aux.(unseal).
Arguments big_opM {M} o {_ K _ _ A} _ _.
Definition big_opM_eq : @big_opM = @big_opM_def := big_opM_aux.(seal_eq).
Instance: Params (@big_opM) 7 := {}.
Notation "'[^' o 'map]' k ↦ x ∈ m , P" := (big_opM o (λ k x, P) m)
  (at level 200, o at level 1, m at level 10, k, x at level 1, right associativity,
   format "[^  o  map]  k ↦ x  ∈  m ,  P") : stdpp_scope.
Notation "'[^' o 'map]' x ∈ m , P" := (big_opM o (λ _ x, P) m)
  (at level 200, o at level 1, m at level 10, x at level 1, right associativity,
   format "[^ o  map]  x  ∈  m ,  P") : stdpp_scope.

Definition big_opS_def `{Monoid M o} `{Countable A} (f : A → M)
  (X : gset A) : M := big_opL o (λ _, f) (elements X).
Definition big_opS_aux : seal (@big_opS_def). Proof. by eexists. Qed.
Definition big_opS := big_opS_aux.(unseal).
Arguments big_opS {M} o {_ A _ _} _ _.
Definition big_opS_eq : @big_opS = @big_opS_def := big_opS_aux.(seal_eq).
Instance: Params (@big_opS) 6 := {}.
Notation "'[^' o 'set]' x ∈ X , P" := (big_opS o (λ x, P) X)
  (at level 200, o at level 1, X at level 10, x at level 1, right associativity,
   format "[^ o  set]  x  ∈  X ,  P") : stdpp_scope.

Definition big_opMS_def `{Monoid M o} `{Countable A} (f : A → M)
  (X : gmultiset A) : M := big_opL o (λ _, f) (elements X).
Definition big_opMS_aux : seal (@big_opMS_def). Proof. by eexists. Qed.
Definition big_opMS := big_opMS_aux.(unseal).
Arguments big_opMS {M} o {_ A _ _} _ _.
Definition big_opMS_eq : @big_opMS = @big_opMS_def := big_opMS_aux.(seal_eq).
Instance: Params (@big_opMS) 6 := {}.
Notation "'[^' o 'mset]' x ∈ X , P" := (big_opMS o (λ x, P) X)
  (at level 200, o at level 1, X at level 10, x at level 1, right associativity,
   format "[^ o  mset]  x  ∈  X ,  P") : stdpp_scope.

(** * Properties about big ops *)
Section big_op.
Context `{Monoid M o}.
Implicit Types xs : list M.
Infix "`o`" := o (at level 50, left associativity).

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : nat → A → M.

  Lemma big_opL_nil f : ([^o list] k↦y ∈ [], f k y) = monoid_unit.
  Proof. done. Qed.
  Lemma big_opL_cons f x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (S k) y.
  Proof. done. Qed.
  Lemma big_opL_singleton f x : ([^o list] k↦y ∈ [x], f k y) ≡ f 0 x.
  Proof. by rewrite /= right_id. Qed.
  Lemma big_opL_app f l1 l2 :
    ([^o list] k↦y ∈ l1 ++ l2, f k y)
    ≡ ([^o list] k↦y ∈ l1, f k y) `o` ([^o list] k↦y ∈ l2, f (length l1 + k) y).
  Proof.
    revert f. induction l1 as [|x l1 IH]=> f /=; first by rewrite left_id.
    by rewrite IH assoc.
  Qed.

  Lemma big_opL_unit l : ([^o list] k↦y ∈ l, monoid_unit) ≡ (monoid_unit : M).
  Proof. induction l; rewrite /= ?left_id //. Qed.

  Lemma big_opL_gen_proper_2 {B} (R : relation M) f (g : nat → B → M)
        l1 (l2 : list B) :
    R monoid_unit monoid_unit →
    Proper (R ==> R ==> R) o →
    (∀ k,
      match l1 !! k, l2 !! k with
      | Some y1, Some y2 => R (f k y1) (g k y2)
      | None, None => True
      | _, _ => False
      end) →
    R ([^o list] k ↦ y ∈ l1, f k y) ([^o list] k ↦ y ∈ l2, g k y).
  Proof.
    intros ??. revert l2 f g. induction l1 as [|x1 l1 IH]=> -[|x2 l2] //= f g Hfg.
    - by specialize (Hfg 0).
    - by specialize (Hfg 0).
    - f_equiv; [apply (Hfg 0)|]. apply IH. intros k. apply (Hfg (S k)).
  Qed.
  Lemma big_opL_gen_proper R f g l :
    Reflexive R →
    Proper (R ==> R ==> R) o →
    (∀ k y, l !! k = Some y → R (f k y) (g k y)) →
    R ([^o list] k ↦ y ∈ l, f k y) ([^o list] k ↦ y ∈ l, g k y).
  Proof.
    intros. apply big_opL_gen_proper_2; [done..|].
    intros k. destruct (l !! k) eqn:?; auto.
  Qed.

  Lemma big_opL_ext f g l :
    (∀ k y, l !! k = Some y → f k y = g k y) →
    ([^o list] k ↦ y ∈ l, f k y) = [^o list] k ↦ y ∈ l, g k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.

  Lemma big_opL_permutation (f : A → M) l1 l2 :
    l1 ≡ₚ l2 → ([^o list] x ∈ l1, f x) ≡ ([^o list] x ∈ l2, f x).
  Proof.
    induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
    - by rewrite IH.
    - by rewrite !assoc (comm _ (f x)).
    - by etrans.
  Qed.
  Global Instance big_opL_permutation' (f : A → M) :
    Proper ((≡ₚ) ==> (≡)) (big_opL o (λ _, f)).
  Proof. intros xs1 xs2. apply big_opL_permutation. Qed.

  (** The lemmas [big_opL_ne] and [big_opL_proper] are more generic than the
  instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_opL_ne f g l n :
    (∀ k y, l !! k = Some y → f k y ≡{n}≡ g k y) →
    ([^o list] k ↦ y ∈ l, f k y) ≡{n}≡ ([^o list] k ↦ y ∈ l, g k y).
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_opL_proper f g l :
    (∀ k y, l !! k = Some y → f k y ≡ g k y) →
    ([^o list] k ↦ y ∈ l, f k y) ≡ ([^o list] k ↦ y ∈ l, g k y).
  Proof. apply big_opL_gen_proper; apply _. Qed.

  (** The version [big_opL_proper_2] with [≡] for the list arguments can only be
  used if there is a setoid on [A]. The version for [dist n] can be found in
  [algebra.list]. We do not define this lemma as a [Proper] instance, since
  [f_equiv] will then use sometimes use this one, and other times
  [big_opL_proper'], depending on whether a setoid on [A] exists. *)
  Lemma big_opL_proper_2 `{!Equiv A} f g l1 l2 :
    l1 ≡ l2 →
    (∀ k y1 y2,
      l1 !! k = Some y1 → l2 !! k = Some y2 → y1 ≡ y2 → f k y1 ≡ g k y2) →
    ([^o list] k ↦ y ∈ l1, f k y) ≡ ([^o list] k ↦ y ∈ l2, g k y).
  Proof.
    intros Hl Hf. apply big_opL_gen_proper_2; try (apply _ || done).
    intros k. assert (l1 !! k ≡ l2 !! k) as Hlk by (by f_equiv).
    destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
  Qed.

  Global Instance big_opL_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (=) ==> dist n)
           (big_opL o (A:=A)).
  Proof. intros f f' Hf l ? <-. apply big_opL_ne; intros; apply Hf. Qed.
  Global Instance big_opL_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (=) ==> (≡))
           (big_opL o (A:=A)).
  Proof. intros f f' Hf l ? <-. apply big_opL_proper; intros; apply Hf. Qed.

  Lemma big_opL_consZ_l (f : Z → A → M) x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (1 + k)%Z y.
  Proof. rewrite big_opL_cons. auto using big_opL_ext with f_equal lia. Qed.
  Lemma big_opL_consZ_r (f : Z → A → M) x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (k + 1)%Z y.
  Proof. rewrite big_opL_cons. auto using big_opL_ext with f_equal lia. Qed.

  Lemma big_opL_fmap {B} (h : A → B) (f : nat → B → M) l :
    ([^o list] k↦y ∈ h <$> l, f k y) ≡ ([^o list] k↦y ∈ l, f k (h y)).
  Proof. revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite IH. Qed.

  Lemma big_opL_op f g l :
    ([^o list] k↦x ∈ l, f k x `o` g k x)
    ≡ ([^o list] k↦x ∈ l, f k x) `o` ([^o list] k↦x ∈ l, g k x).
  Proof.
    revert f g; induction l as [|x l IH]=> f g /=; first by rewrite left_id.
    by rewrite IH -!assoc (assoc _ (g _ _)) [(g _ _ `o` _)]comm -!assoc.
  Qed.
End list.

Lemma big_opL_bind {A B} (h : A → list B) (f : B → M) l :
  ([^o list] y ∈ l ≫= h, f y) ≡ ([^o list] x ∈ l, [^o list] y ∈ h x, f y).
Proof.
  revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite big_opL_app IH.
Qed.

(** ** Big ops over finite maps *)

Lemma big_opM_empty `{Countable K} {B} (f : K → B → M) :
  ([^o map] k↦x ∈ ∅, f k x) = monoid_unit.
Proof. by rewrite big_opM_eq /big_opM_def map_to_list_empty. Qed.

Lemma big_opM_insert `{Countable K} {B} (f : K → B → M) (m : gmap K B) i x :
  m !! i = None →
  ([^o map] k↦y ∈ <[i:=x]> m, f k y) ≡ f i x `o` [^o map] k↦y ∈ m, f k y.
Proof. intros ?. by rewrite big_opM_eq /big_opM_def map_to_list_insert. Qed.

Lemma big_opM_delete `{Countable K} {B} (f : K → B → M) (m : gmap K B) i x :
  m !! i = Some x →
  ([^o map] k↦y ∈ m, f k y) ≡ f i x `o` [^o map] k↦y ∈ delete i m, f k y.
Proof.
  intros. rewrite -big_opM_insert ?lookup_delete //.
  by rewrite insert_delete insert_id.
Qed.

Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types f g : K → A → M.

  Lemma big_opM_gen_proper_2 {B} (R : relation M) f (g : K → B → M)
        m1 (m2 : gmap K B) :
    subrelation (≡) R → Equivalence R →
    Proper (R ==> R ==> R) o →
    (∀ k,
      match m1 !! k, m2 !! k with
      | Some y1, Some y2 => R (f k y1) (g k y2)
      | None, None => True
      | _, _ => False
      end) →
    R ([^o map] k ↦ x ∈ m1, f k x) ([^o map] k ↦ x ∈ m2, g k x).
  Proof.
    intros HR ??. revert m2 f g.
    induction m1 as [|k x1 m1 Hm1k IH] using map_ind=> m2 f g Hfg.
    { destruct m2 as [|k x2 m2 _ _] using map_ind.
      { rewrite !big_opM_empty. by apply HR. }
      generalize (Hfg k). by rewrite lookup_empty lookup_insert. }
    generalize (Hfg k). rewrite lookup_insert.
    destruct (m2 !! k) as [x2|] eqn:Hm2k; [intros Hk|done].
    etrans; [by apply HR, big_opM_insert|].
    etrans; [|by symmetry; apply HR, big_opM_delete].
    f_equiv; [done|]. apply IH=> k'. destruct (decide (k = k')) as [->|?].
    - by rewrite lookup_delete Hm1k.
    - generalize (Hfg k'). rewrite lookup_insert_ne // lookup_delete_ne //.
  Qed.

  Lemma big_opM_gen_proper R f g m :
    Reflexive R →
    Proper (R ==> R ==> R) o →
    (∀ k x, m !! k = Some x → R (f k x) (g k x)) →
    R ([^o map] k ↦ x ∈ m, f k x) ([^o map] k ↦ x ∈ m, g k x).
  Proof.
    intros ?? Hf. rewrite big_opM_eq. apply (big_opL_gen_proper R); auto.
    intros k [i x] ?%elem_of_list_lookup_2. by apply Hf, elem_of_map_to_list.
  Qed.

  Lemma big_opM_ext f g m :
    (∀ k x, m !! k = Some x → f k x = g k x) →
    ([^o map] k ↦ x ∈ m, f k x) = ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_gen_proper; apply _. Qed.

  (** The lemmas [big_opM_ne] and [big_opM_proper] are more generic than the
  instances as they also give [m !! k = Some y] in the premise. *)
  Lemma big_opM_ne f g m n :
    (∀ k x, m !! k = Some x → f k x ≡{n}≡ g k x) →
    ([^o map] k ↦ x ∈ m, f k x) ≡{n}≡ ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_gen_proper; apply _. Qed.
  Lemma big_opM_proper f g m :
    (∀ k x, m !! k = Some x → f k x ≡ g k x) →
    ([^o map] k ↦ x ∈ m, f k x) ≡ ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_gen_proper; apply _. Qed.
  (** The version [big_opM_proper_2] with [≡] for the map arguments can only be
  used if there is a setoid on [A]. The version for [dist n] can be found in
  [algebra.gmap]. We do not define this lemma as a [Proper] instance, since
  [f_equiv] will then use sometimes use this one, and other times
  [big_opM_proper'], depending on whether a setoid on [A] exists. *)
  Lemma big_opM_proper_2 `{!Equiv A} f g m1 m2 :
    m1 ≡ m2 →
    (∀ k y1 y2,
      m1 !! k = Some y1 → m2 !! k = Some y2 → y1 ≡ y2 → f k y1 ≡ g k y2) →
    ([^o map] k ↦ y ∈ m1, f k y) ≡ ([^o map] k ↦ y ∈ m2, g k y).
  Proof.
    intros Hl Hf. apply big_opM_gen_proper_2; try (apply _ || done).
    intros k. assert (m1 !! k ≡ m2 !! k) as Hlk by (by f_equiv).
    destruct (m1 !! k) eqn:?, (m2 !! k) eqn:?; inversion Hlk; naive_solver.
  Qed.

  Global Instance big_opM_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (=) ==> dist n)
           (big_opM o (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opM_ne; intros; apply Hf. Qed.
  Global Instance big_opM_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (=) ==> (≡))
           (big_opM o (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opM_proper; intros; apply Hf. Qed.

  Lemma big_opM_singleton f i x : ([^o map] k↦y ∈ {[i:=x]}, f k y) ≡ f i x.
  Proof.
    rewrite -insert_empty big_opM_insert/=; last eauto using lookup_empty.
    by rewrite big_opM_empty right_id.
  Qed.

  Lemma big_opM_unit m : ([^o map] k↦y ∈ m, monoid_unit) ≡ (monoid_unit : M).
  Proof. by induction m using map_ind; rewrite /= ?big_opM_insert ?left_id // big_opM_eq. Qed.

  Lemma big_opM_fmap {B} (h : A → B) (f : K → B → M) m :
    ([^o map] k↦y ∈ h <$> m, f k y) ≡ ([^o map] k↦y ∈ m, f k (h y)).
  Proof.
    rewrite big_opM_eq /big_opM_def map_to_list_fmap big_opL_fmap.
    by apply big_opL_proper=> ? [??].
  Qed.

  Lemma big_opM_insert_delete `{Countable K} {B} (f : K → B → M) (m : gmap K B) i x :
    ([^o map] k↦y ∈ <[i:=x]> m, f k y) ≡ f i x `o` [^o map] k↦y ∈ delete i m, f k y.
  Proof.
    rewrite -insert_delete big_opM_insert; first done. by rewrite lookup_delete.
  Qed.

  Lemma big_opM_insert_override (f : K → A → M) m i x x' :
    m !! i = Some x → f i x ≡ f i x' →
    ([^o map] k↦y ∈ <[i:=x']> m, f k y) ≡ ([^o map] k↦y ∈ m, f k y).
  Proof.
    intros ? Hx. rewrite -insert_delete big_opM_insert ?lookup_delete //.
    by rewrite -Hx -big_opM_delete.
  Qed.

  Lemma big_opM_fn_insert {B} (g : K → A → B → M) (f : K → B) m i (x : A) b :
    m !! i = None →
    ([^o map] k↦y ∈ <[i:=x]> m, g k y (<[i:=b]> f k))
    ≡ g i x b `o` [^o map] k↦y ∈ m, g k y (f k).
  Proof.
    intros. rewrite big_opM_insert // fn_lookup_insert.
    f_equiv; apply big_opM_proper; auto=> k y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opM_fn_insert' (f : K → M) m i x P :
    m !! i = None →
    ([^o map] k↦y ∈ <[i:=x]> m, <[i:=P]> f k) ≡ (P `o` [^o map] k↦y ∈ m, f k).
  Proof. apply (big_opM_fn_insert (λ _ _, id)). Qed.

  Lemma big_opM_union f m1 m2 :
    m1 ##ₘ m2 →
    ([^o map] k↦y ∈ m1 ∪ m2, f k y) ≡ ([^o map] k↦y ∈ m1, f k y) `o` ([^o map] k↦y ∈ m2, f k y).
  Proof.
    intros. induction m1 as [|i x m ? IH] using map_ind.
    { by rewrite big_opM_empty !left_id. }
    decompose_map_disjoint.
    rewrite -insert_union_l !big_opM_insert //;
      last by apply lookup_union_None.
    rewrite -assoc IH //.
  Qed.

  Lemma big_opM_op f g m :
    ([^o map] k↦x ∈ m, f k x `o` g k x)
    ≡ ([^o map] k↦x ∈ m, f k x) `o` ([^o map] k↦x ∈ m, g k x).
  Proof. rewrite big_opM_eq /big_opM_def -big_opL_op. by apply big_opL_proper=> ? [??]. Qed.
End gmap.


(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

  Lemma big_opS_gen_proper R f g X :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ x, x ∈ X → R (f x) (g x)) →
    R ([^o set] x ∈ X, f x) ([^o set] x ∈ X, g x).
  Proof.
    rewrite big_opS_eq. intros ?? Hf. apply (big_opL_gen_proper R); auto.
    intros k x ?%elem_of_list_lookup_2. by apply Hf, elem_of_elements.
  Qed.

  Lemma big_opS_ext f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^o set] x ∈ X, f x) = ([^o set] x ∈ X, g x).
  Proof. apply big_opS_gen_proper; apply _. Qed.

  (** The lemmas [big_opS_ne] and [big_opS_proper] are more generic than the
  instances as they also give [x ∈ X] in the premise. *)
  Lemma big_opS_ne f g X n :
    (∀ x, x ∈ X → f x ≡{n}≡ g x) →
    ([^o set] x ∈ X, f x) ≡{n}≡ ([^o set] x ∈ X, g x).
  Proof. apply big_opS_gen_proper; apply _. Qed.
  Lemma big_opS_proper f g X :
    (∀ x, x ∈ X → f x ≡ g x) →
    ([^o set] x ∈ X, f x) ≡ ([^o set] x ∈ X, g x).
  Proof. apply big_opS_gen_proper; apply _. Qed.

  Global Instance big_opS_ne' n :
    Proper (pointwise_relation _ (dist n) ==> (=) ==> dist n) (big_opS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opS_ne; intros; apply Hf. Qed.
  Global Instance big_opS_proper' :
    Proper (pointwise_relation _ (≡) ==> (=) ==> (≡)) (big_opS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opS_proper; intros; apply Hf. Qed.

  Lemma big_opS_empty f : ([^o set] x ∈ ∅, f x) = monoid_unit.
  Proof. by rewrite big_opS_eq /big_opS_def elements_empty. Qed.

  Lemma big_opS_insert f X x :
    x ∉ X → ([^o set] y ∈ {[ x ]} ∪ X, f y) ≡ (f x `o` [^o set] y ∈ X, f y).
  Proof. intros. by rewrite big_opS_eq /big_opS_def elements_union_singleton. Qed.
  Lemma big_opS_fn_insert {B} (f : A → B → M) h X x b :
    x ∉ X →
    ([^o set] y ∈ {[ x ]} ∪ X, f y (<[x:=b]> h y))
    ≡ f x b `o` [^o set] y ∈ X, f y (h y).
  Proof.
    intros. rewrite big_opS_insert // fn_lookup_insert.
    f_equiv; apply big_opS_proper; auto=> y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opS_fn_insert' f X x P :
    x ∉ X → ([^o set] y ∈ {[ x ]} ∪ X, <[x:=P]> f y) ≡ (P `o` [^o set] y ∈ X, f y).
  Proof. apply (big_opS_fn_insert (λ y, id)). Qed.

  Lemma big_opS_union f X Y :
    X ## Y →
    ([^o set] y ∈ X ∪ Y, f y) ≡ ([^o set] y ∈ X, f y) `o` ([^o set] y ∈ Y, f y).
  Proof.
    intros. induction X as [|x X ? IH] using set_ind_L.
    { by rewrite left_id_L big_opS_empty left_id. }
    rewrite -assoc_L !big_opS_insert; [|set_solver..].
    by rewrite -assoc IH; last set_solver.
  Qed.

  Lemma big_opS_delete f X x :
    x ∈ X → ([^o set] y ∈ X, f y) ≡ f x `o` [^o set] y ∈ X ∖ {[ x ]}, f y.
  Proof.
    intros. rewrite -big_opS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.

  Lemma big_opS_singleton f x : ([^o set] y ∈ {[ x ]}, f y) ≡ f x.
  Proof. intros. by rewrite big_opS_eq /big_opS_def elements_singleton /= right_id. Qed.

  Lemma big_opS_unit X : ([^o set] y ∈ X, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    by induction X using set_ind_L; rewrite /= ?big_opS_insert ?left_id // big_opS_eq.
  Qed.

  Lemma big_opS_op f g X :
    ([^o set] y ∈ X, f y `o` g y) ≡ ([^o set] y ∈ X, f y) `o` ([^o set] y ∈ X, g y).
  Proof. by rewrite big_opS_eq /big_opS_def -big_opL_op. Qed.
End gset.

Lemma big_opM_dom `{Countable K} {A} (f : K → M) (m : gmap K A) :
  ([^o map] k↦_ ∈ m, f k) ≡ ([^o set] k ∈ dom _ m, f k).
Proof.
  induction m as [|i x ?? IH] using map_ind; [by rewrite big_opM_eq big_opS_eq dom_empty_L|].
  by rewrite dom_insert_L big_opM_insert // IH big_opS_insert ?not_elem_of_dom.
Qed.

(** ** Big ops over finite msets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types f : A → M.

  Lemma big_opMS_gen_proper R f g X :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ x, x ∈ X → R (f x) (g x)) →
    R ([^o mset] x ∈ X, f x) ([^o mset] x ∈ X, g x).
  Proof.
    rewrite big_opMS_eq. intros ?? Hf. apply (big_opL_gen_proper R); auto.
    intros k x ?%elem_of_list_lookup_2. by apply Hf, gmultiset_elem_of_elements.
  Qed.

  Lemma big_opMS_ext f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^o mset] x ∈ X, f x) = ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_gen_proper; apply _. Qed.

  (** The lemmas [big_opMS_ne] and [big_opMS_proper] are more generic than the
  instances as they also give [x ∈ X] in the premise. *)
  Lemma big_opMS_ne f g X n :
    (∀ x, x ∈ X → f x ≡{n}≡ g x) →
    ([^o mset] x ∈ X, f x) ≡{n}≡ ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_gen_proper; apply _. Qed.
  Lemma big_opMS_proper f g X :
    (∀ x, x ∈ X → f x ≡ g x) →
    ([^o mset] x ∈ X, f x) ≡ ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_gen_proper; apply _. Qed.

  Global Instance big_opMS_ne' n :
    Proper (pointwise_relation _ (dist n) ==> (=) ==> dist n) (big_opMS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opMS_ne; intros; apply Hf. Qed.
  Global Instance big_opMS_proper' :
    Proper (pointwise_relation _ (≡) ==> (=) ==> (≡)) (big_opMS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opMS_proper; intros; apply Hf. Qed.

  Lemma big_opMS_empty f : ([^o mset] x ∈ ∅, f x) = monoid_unit.
  Proof. by rewrite big_opMS_eq /big_opMS_def gmultiset_elements_empty. Qed.

  Lemma big_opMS_disj_union f X Y :
    ([^o mset] y ∈ X ⊎ Y, f y) ≡ ([^o mset] y ∈ X, f y) `o` [^o mset] y ∈ Y, f y.
  Proof. by rewrite big_opMS_eq /big_opMS_def gmultiset_elements_disj_union big_opL_app. Qed.

  Lemma big_opMS_singleton f x : ([^o mset] y ∈ {[ x ]}, f y) ≡ f x.
  Proof.
    intros. by rewrite big_opMS_eq /big_opMS_def gmultiset_elements_singleton /= right_id.
  Qed.

  Lemma big_opMS_delete f X x :
    x ∈ X → ([^o mset] y ∈ X, f y) ≡ f x `o` [^o mset] y ∈ X ∖ {[ x ]}, f y.
  Proof.
    intros. rewrite -big_opMS_singleton -big_opMS_disj_union.
    by rewrite -gmultiset_disj_union_difference'.
  Qed.

  Lemma big_opMS_unit X : ([^o mset] y ∈ X, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    by induction X using gmultiset_ind;
      rewrite /= ?big_opMS_disj_union ?big_opMS_singleton ?left_id // big_opMS_eq.
  Qed.

  Lemma big_opMS_op f g X :
    ([^o mset] y ∈ X, f y `o` g y) ≡ ([^o mset] y ∈ X, f y) `o` ([^o mset] y ∈ X, g y).
  Proof. by rewrite big_opMS_eq /big_opMS_def -big_opL_op. Qed.
End gmultiset.
End big_op.

Section homomorphisms.
  Context `{Monoid M1 o1, Monoid M2 o2}.
  Infix "`o1`" := o1 (at level 50, left associativity).
  Infix "`o2`" := o2 (at level 50, left associativity).
  (** The ssreflect rewrite tactic only works for relations that have a
  [RewriteRelation] instance. For the purpose of this section, we want to
  rewrite with arbitrary relations, so we declare any relation to be a
  [RewriteRelation]. *)
  Local Instance: ∀ {A} (R : relation A), RewriteRelation R := {}.

  Lemma big_opL_commute {A} (h : M1 → M2) `{!MonoidHomomorphism o1 o2 R h}
      (f : nat → A → M1) l :
    R (h ([^o1 list] k↦x ∈ l, f k x)) ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof.
    revert f. induction l as [|x l IH]=> f /=.
    - apply monoid_homomorphism_unit.
    - by rewrite monoid_homomorphism IH.
  Qed.
  Lemma big_opL_commute1 {A} (h : M1 → M2) `{!WeakMonoidHomomorphism o1 o2 R h}
      (f : nat → A → M1) l :
    l ≠ [] → R (h ([^o1 list] k↦x ∈ l, f k x)) ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof.
    intros ?. revert f. induction l as [|x [|x' l'] IH]=> f //.
    - by rewrite !big_opL_singleton.
    - by rewrite !(big_opL_cons _ x) monoid_homomorphism IH.
  Qed.

  Lemma big_opM_commute `{Countable K} {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : K → A → M1) m :
    R (h ([^o1 map] k↦x ∈ m, f k x)) ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof.
    intros. induction m as [|i x m ? IH] using map_ind.
    - by rewrite !big_opM_empty monoid_homomorphism_unit.
    - by rewrite !big_opM_insert // monoid_homomorphism -IH.
  Qed.
  Lemma big_opM_commute1 `{Countable K} {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : K → A → M1) m :
    m ≠ ∅ → R (h ([^o1 map] k↦x ∈ m, f k x)) ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof.
    intros. induction m as [|i x m ? IH] using map_ind; [done|].
    destruct (decide (m = ∅)) as [->|].
    - by rewrite !big_opM_insert // !big_opM_empty !right_id.
    - by rewrite !big_opM_insert // monoid_homomorphism -IH //.
  Qed.

  Lemma big_opS_commute `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    R (h ([^o1 set] x ∈ X, f x)) ([^o2 set] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X ? IH] using set_ind_L.
    - by rewrite !big_opS_empty monoid_homomorphism_unit.
    - by rewrite !big_opS_insert // monoid_homomorphism -IH.
  Qed.
  Lemma big_opS_commute1 `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    X ≠ ∅ → R (h ([^o1 set] x ∈ X, f x)) ([^o2 set] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X ? IH] using set_ind_L; [done|].
    destruct (decide (X = ∅)) as [->|].
    - by rewrite !big_opS_insert // !big_opS_empty !right_id.
    - by rewrite !big_opS_insert // monoid_homomorphism -IH //.
  Qed.

  Lemma big_opMS_commute `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    R (h ([^o1 mset] x ∈ X, f x)) ([^o2 mset] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X IH] using gmultiset_ind.
    - by rewrite !big_opMS_empty monoid_homomorphism_unit.
    - by rewrite !big_opMS_disj_union !big_opMS_singleton monoid_homomorphism -IH.
  Qed.
  Lemma big_opMS_commute1 `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    X ≠ ∅ → R (h ([^o1 mset] x ∈ X, f x)) ([^o2 mset] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X IH] using gmultiset_ind; [done|].
    destruct (decide (X = ∅)) as [->|].
    - by rewrite !big_opMS_disj_union !big_opMS_singleton !big_opMS_empty !right_id.
    - by rewrite !big_opMS_disj_union !big_opMS_singleton monoid_homomorphism -IH //.
  Qed.

  Context `{!LeibnizEquiv M2}.

  Lemma big_opL_commute_L {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : nat → A → M1) l :
    h ([^o1 list] k↦x ∈ l, f k x) = ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opL_commute. Qed.
  Lemma big_opL_commute1_L {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : nat → A → M1) l :
    l ≠ [] → h ([^o1 list] k↦x ∈ l, f k x) = ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opL_commute1. Qed.

  Lemma big_opM_commute_L `{Countable K} {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : K → A → M1) m :
    h ([^o1 map] k↦x ∈ m, f k x) = ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opM_commute. Qed.
  Lemma big_opM_commute1_L `{Countable K} {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : K → A → M1) m :
    m ≠ ∅ → h ([^o1 map] k↦x ∈ m, f k x) = ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opM_commute1. Qed.

  Lemma big_opS_commute_L `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    h ([^o1 set] x ∈ X, f x) = ([^o2 set] x ∈ X, h (f x)).
  Proof using Type*. unfold_leibniz. by apply big_opS_commute. Qed.
  Lemma big_opS_commute1_L `{ Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    X ≠ ∅ → h ([^o1 set] x ∈ X, f x) = ([^o2 set] x ∈ X, h (f x)).
  Proof using Type*. intros. rewrite <-leibniz_equiv_iff. by apply big_opS_commute1. Qed.

  Lemma big_opMS_commute_L `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    h ([^o1 mset] x ∈ X, f x) = ([^o2 mset] x ∈ X, h (f x)).
  Proof using Type*. unfold_leibniz. by apply big_opMS_commute. Qed.
  Lemma big_opMS_commute1_L `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    X ≠ ∅ → h ([^o1 mset] x ∈ X, f x) = ([^o2 mset] x ∈ X, h (f x)).
  Proof using Type*. intros. rewrite <-leibniz_equiv_iff. by apply big_opMS_commute1. Qed.
End homomorphisms.
