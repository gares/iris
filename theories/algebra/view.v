From iris.proofmode Require Import tactics.
From iris.algebra Require Export frac agree local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.base_logic Require Import base_logic.
From iris Require Import options.

(** The view camera with fractional authoritative parts. The camera [view] has
3 types of elements: the fractional authoritative [●V{q} a], the full
authoritative [●V a ≡ ●V{1} a], and the non-authoritative [◯V a]. Updates are
only possible with the full authoritative element [●V a], while fractional
authoritative elements have agreement: [✓ (●V{p} a ⋅ ●V{q} b) → a ≡ b]. *)

(** * The view relation *)
(** The view camera is parametrized by a (step-indexed) relation
[view_rel n a b] that relates the authoritative element [a] to the composition
of all fragments [b]. This relation should be a.) down-closed w.r.t. the
step-indexed [n], b.) non-expansive w.r.t. the argument [a], c.) monotone w.r.t.
the argument [b], d.) ensure validity of the argument [b]. *)
Structure view_rel (A : ofeT) (B : ucmraT) := ViewRel {
  view_rel_holds :> nat → A → B → Prop;
  view_rel_mono n1 n2 a1 a2 b1 b2 :
    view_rel_holds n1 a1 b1 →
    a1 ≡{n1}≡ a2 → b2 ≼{n1} b1 → n2 ≤ n1 → view_rel_holds n2 a2 b2;
  view_rel_validN n a b :
    view_rel_holds n a b → ✓{n} b
}.
Arguments ViewRel {_ _} _ _.
Arguments view_rel_holds {_ _} _ _ _ _.
Instance: Params (@view_rel) 4 := {}.

Instance view_rel_ne {A B} (rel : view_rel A B) n :
  Proper (dist n ==> dist n ==> iff) (rel n).
Proof.
  intros a1 a2 Ha b1 b2 Hb.
  split=> ?; (eapply view_rel_mono; [done|done|by rewrite Hb|done]).
Qed.
Instance view_rel_proper {A B} (rel : view_rel A B) n :
  Proper ((≡) ==> (≡) ==> iff) (rel n).
Proof. intros a1 a2 Ha b1 b2 Hb. apply view_rel_ne; by apply equiv_dist. Qed.

Class ViewRelDiscrete {A B} (rel : view_rel A B) :=
  view_rel_discrete n a b : rel 0 a b → rel n a b.

(** * Definition of the view camera *)
Record view {A B} (rel : nat → A → B → Prop) :=
  View { view_auth_proj : option (frac * agree A) ; view_frag_proj : B }.
Add Printing Constructor view.
Arguments View {_ _ _} _ _.
Arguments view_auth_proj {_ _ _} _.
Arguments view_frag_proj {_ _ _} _.
Instance: Params (@View) 3 := {}.
Instance: Params (@view_auth_proj) 3 := {}.
Instance: Params (@view_frag_proj) 3 := {}.

Definition view_auth {A B} {rel : view_rel A B} (q : Qp) (a : A) : view rel :=
  View (Some (q, to_agree a)) ε.
Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel := View None b.
Typeclasses Opaque view_auth view_frag.

Instance: Params (@view_auth) 3 := {}.
Instance: Params (@view_frag) 3 := {}.

Notation "●V{ q } a" := (view_auth q a) (at level 20, format "●V{ q }  a").
Notation "●V a" := (view_auth 1 a) (at level 20).
Notation "◯V a" := (view_frag a) (at level 20).

(** * Ofe *)
Section ofe.
  Context {A B : ofeT} (rel : nat → A → B → Prop).
  Implicit Types a : A.
  Implicit Types ag : option (frac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.

  Instance view_equiv : Equiv (view rel) := λ x y,
    view_auth_proj x ≡ view_auth_proj y ∧ view_frag_proj x ≡ view_frag_proj y.
  Instance view_dist : Dist (view rel) := λ n x y,
    view_auth_proj x ≡{n}≡ view_auth_proj y ∧
    view_frag_proj x ≡{n}≡ view_frag_proj y.

  Global Instance View_ne : NonExpansive2 (@View A B rel).
  Proof. by split. Qed.
  Global Instance View_proper : Proper ((≡) ==> (≡) ==> (≡)) (@View A B rel).
  Proof. by split. Qed.
  Global Instance view_auth_proj_ne: NonExpansive (@view_auth_proj A B rel).
  Proof. by destruct 1. Qed.
  Global Instance view_auth_proj_proper :
    Proper ((≡) ==> (≡)) (@view_auth_proj A B rel).
  Proof. by destruct 1. Qed.
  Global Instance view_frag_proj_ne : NonExpansive (@view_frag_proj A B rel).
  Proof. by destruct 1. Qed.
  Global Instance view_frag_proj_proper :
    Proper ((≡) ==> (≡)) (@view_frag_proj A B rel).
  Proof. by destruct 1. Qed.

  Definition view_ofe_mixin : OfeMixin (view rel).
  Proof. by apply (iso_ofe_mixin (λ x, (view_auth_proj x, view_frag_proj x))). Qed.
  Canonical Structure viewO := OfeT (view rel) view_ofe_mixin.

  Global Instance View_discrete ag b :
    Discrete ag → Discrete b → Discrete (View ag b).
  Proof. by intros ?? [??] [??]; split; apply: discrete. Qed.
  Global Instance view_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete viewO.
  Proof. intros ?? [??]; apply _. Qed.

  (** Internalized properties *)
  Lemma view_equivI {M} x y :
    x ≡ y ⊣⊢@{uPredI M}
      view_auth_proj x ≡ view_auth_proj y ∧ view_frag_proj x ≡ view_frag_proj y.
  Proof. by uPred.unseal. Qed.
End ofe.

(** * Camera *)
Section cmra.
  Context {A B} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types ag : option (frac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.

  Global Instance view_frag_ne: NonExpansive (@view_frag A B rel).
  Proof. done. Qed.
  Global Instance view_frag_proper : Proper ((≡) ==> (≡)) (@view_frag A B rel).
  Proof. done. Qed.
  Global Instance view_auth_ne q : NonExpansive (@view_auth A B rel q).
  Proof. solve_proper. Qed.
  Global Instance view_auth_proper q : Proper ((≡) ==> (≡)) (@view_auth A B rel q).
  Proof. solve_proper. Qed.

  Instance view_valid : Valid (view rel) := λ x,
    match view_auth_proj x with
    | Some (q, ag) =>
       ✓ q ∧ (∀ n, ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x))
    | None => ✓ view_frag_proj x
    end.
  Instance view_validN : ValidN (view rel) := λ n x,
    match view_auth_proj x with
    | Some (q, ag) =>
       ✓{n} q ∧ ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x)
    | None => ✓{n} view_frag_proj x
    end.
  Instance view_pcore : PCore (view rel) := λ x,
    Some (View (core (view_auth_proj x)) (core (view_frag_proj x))).
  Instance view_op : Op (view rel) := λ x y,
    View (view_auth_proj x ⋅ view_auth_proj y) (view_frag_proj x ⋅ view_frag_proj y).

  Definition view_valid_eq :
    valid = λ x,
      match view_auth_proj x with
      | Some (q, ag) =>
         ✓ q ∧ (∀ n, ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x))
      | None => ✓ view_frag_proj x
      end := eq_refl _.
  Definition view_validN_eq :
    validN = λ n x, 
      match view_auth_proj x with
      | Some (q, ag) => ✓{n} q ∧ ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x)
      | None => ✓{n} view_frag_proj x
      end := eq_refl _.

  Lemma view_auth_frac_validN n q a : ✓{n} (●V{q} a) ↔ ✓{n} q ∧ rel n a ε.
  Proof.
    rewrite view_validN_eq /=. apply and_iff_compat_l. split; [|by eauto].
    by intros [? [->%(inj to_agree) ?]].
  Qed.
  Lemma view_auth_validN n a : ✓{n} (●V a) ↔ rel n a ε.
  Proof.
    rewrite view_auth_frac_validN -cmra_discrete_valid_iff frac_valid'. naive_solver.
  Qed.
  Lemma view_frag_validN n b : ✓{n} (◯V b) ↔ ✓{n} b.
  Proof. done. Qed.
  Lemma view_both_frac_validN n q a b :
    ✓{n} (●V{q} a ⋅ ◯V b) ↔ ✓{n} q ∧ rel n a b.
  Proof.
    rewrite view_validN_eq /=. apply and_iff_compat_l.
    setoid_rewrite (left_id _ _ b). split; [|by eauto].
    by intros [?[->%(inj to_agree)]].
  Qed.
  Lemma view_both_validN n a b : ✓{n} (●V a ⋅ ◯V b) ↔ rel n a b.
  Proof.
    rewrite view_both_frac_validN -cmra_discrete_valid_iff frac_valid'. naive_solver.
  Qed.

  Lemma view_auth_frac_valid q a : ✓ (●V{q} a) ↔ ✓ q ∧ ∀ n, rel n a ε.
  Proof.
    rewrite view_valid_eq /=. apply and_iff_compat_l. split; [|by eauto].
    intros H n. by destruct (H n) as [? [->%(inj to_agree) ?]].
  Qed.
  Lemma view_auth_valid a : ✓ (●V a) ↔ ∀ n, rel n a ε.
  Proof. rewrite view_auth_frac_valid frac_valid'. naive_solver. Qed.
  Lemma view_frag_valid b : ✓ (◯V b) ↔ ✓ b.
  Proof. done. Qed.
  Lemma view_both_frac_valid q a b : ✓ (●V{q} a ⋅ ◯V b) ↔ ✓ q ∧ ∀ n, rel n a b.
  Proof.
    rewrite view_valid_eq /=. apply and_iff_compat_l.
    setoid_rewrite (left_id _ _ b). split; [|by eauto].
    intros H n. by destruct (H n) as [?[->%(inj to_agree)]].
  Qed.
  Lemma view_both_valid a b : ✓ (●V a ⋅ ◯V b) ↔ ∀ n, rel n a b.
  Proof. rewrite view_both_frac_valid frac_valid'. naive_solver. Qed.

  Lemma view_cmra_mixin : CmraMixin (view rel).
  Proof.
    apply (iso_cmra_mixin_restrict
      (λ x : option (frac * agree A) * B, View x.1 x.2)
      (λ x, (view_auth_proj x, view_frag_proj x))); try done.
    - intros [x b]. by rewrite /= pair_pcore !cmra_pcore_core.
    - intros n [[[q ag]|] b]; rewrite /= view_validN_eq /=; last done.
      intros (?&a&->&?). repeat split; simpl; [done|]. by eapply view_rel_validN.
    - rewrite view_validN_eq.
      intros n [x1 b1] [x2 b2] [Hx ?]; simpl in *;
        destruct Hx as [[q1 ag1] [q2 ag2] [??]|]; intros ?; by ofe_subst.
    - rewrite view_valid_eq view_validN_eq.
      intros [[[q aa]|] b]; rewrite /= cmra_valid_validN; naive_solver.
    - rewrite view_validN_eq=> n [[[q ag]|] b] /=; [|by eauto using cmra_validN_S].
      intros [? (a&?&?)]; split; [done|]. exists a; split; [by eauto using dist_S|].
      apply view_rel_mono with (S n) a b; auto with lia.
    - rewrite view_validN_eq=> n [[[q1 ag1]|] b1] [[[q2 ag2]|] b2] /=.
      + intros [?%cmra_validN_op_l (a & Haga & ?)]. split; [done|].
        assert (ag1 ≡{n}≡ ag2) as Ha12 by (apply agree_op_invN; by rewrite Haga).
        exists a. split; [by rewrite -Haga -Ha12 agree_idemp|].
        apply view_rel_mono with n a (b1 ⋅ b2); eauto using cmra_includedN_l.
      + intros [? (a & Haga & ?)]. split; [done|]. exists a; split; [done|].
        apply view_rel_mono with n a (b1 ⋅ b2); eauto using cmra_includedN_l.
      + intros [? (a & Haga & ?%view_rel_validN)]. eauto using cmra_validN_op_l.
      + eauto using cmra_validN_op_l.
  Qed.
  Canonical Structure viewR := CmraT (view rel) view_cmra_mixin.

  Global Instance view_auth_discrete q a :
    Discrete a → Discrete (ε : B) → Discrete (●V{q} a : view rel).
  Proof. intros. apply View_discrete; apply _. Qed.
  Global Instance view_frag_discrete b :
    Discrete b → Discrete (◯V b : view rel).
  Proof. intros. apply View_discrete; apply _. Qed.
  Global Instance view_cmra_discrete :
    OfeDiscrete A → CmraDiscrete B → ViewRelDiscrete rel →
    CmraDiscrete viewR.
  Proof.
    split; [apply _|]=> -[[[q ag]|] b]; rewrite view_valid_eq view_validN_eq /=.
    - rewrite -cmra_discrete_valid_iff.
      setoid_rewrite <-(discrete_iff _ ag). naive_solver.
    - by rewrite -cmra_discrete_valid_iff.
  Qed.

  Instance view_empty : Unit (view rel) := View ε ε.
  Lemma view_ucmra_mixin : UcmraMixin (view rel).
  Proof.
    split; simpl.
    - rewrite view_valid_eq /=. apply ucmra_unit_valid.
    - by intros x; constructor; rewrite /= left_id.
    - do 2 constructor; [done| apply (core_id_core _)].
  Qed.
  Canonical Structure viewUR := UcmraT (view rel) view_ucmra_mixin.

  Lemma view_auth_frac_op p1 p2 a : ●V{p1 + p2} a ≡ ●V{p1} a ⋅ ●V{p2} a.
  Proof.
    intros; split; simpl; last by rewrite left_id.
    by rewrite -Some_op -pair_op agree_idemp.
  Qed.
  Lemma view_auth_frac_op_invN n p1 a1 p2 a2 :
    ✓{n} (●V{p1} a1 ⋅ ●V{p2} a2) → a1 ≡{n}≡ a2.
  Proof.
    rewrite /op /view_op /= left_id -Some_op -pair_op view_validN_eq /=.
    intros (?&?& Eq &?). apply (inj to_agree), agree_op_invN. by rewrite Eq.
  Qed.
  Lemma view_auth_frac_op_inv p1 a1 p2 a2 : ✓ (●V{p1} a1 ⋅ ●V{p2} a2) → a1 ≡ a2.
  Proof.
    intros ?. apply equiv_dist. intros n.
    by eapply view_auth_frac_op_invN, cmra_valid_validN.
  Qed.
  Lemma view_auth_frac_op_inv_L `{!LeibnizEquiv A} p1 a1 p2 a2 :
    ✓ (●V{p1} a1 ⋅ ●V{p2} a2) → a1 = a2.
  Proof. by intros ?%view_auth_frac_op_inv%leibniz_equiv. Qed.
  Global Instance is_op_view_auth_frac q q1 q2 a :
    IsOp q q1 q2 → IsOp' (●V{q} a) (●V{q1} a) (●V{q2} a).
  Proof. rewrite /IsOp' /IsOp => ->. by rewrite -view_auth_frac_op. Qed.

  Lemma view_frag_op b1 b2 : ◯V (b1 ⋅ b2) = ◯V b1 ⋅ ◯V b2.
  Proof. done. Qed.
  Lemma view_frag_mono b1 b2 : b1 ≼ b2 → ◯V b1 ≼ ◯V b2.
  Proof. intros [c ->]. rewrite view_frag_op. apply cmra_included_l. Qed.
  Lemma view_frag_core b : core (◯V b) = ◯V (core b).
  Proof. done. Qed.
  Global Instance view_frag_core_id b : CoreId b → CoreId (◯V b).
  Proof. do 2 constructor; simpl; auto. by apply core_id_core. Qed.
  Global Instance is_op_view_frag b b1 b2 :
    IsOp b b1 b2 → IsOp' (◯V b) (◯V b1) (◯V b2).
  Proof. done. Qed.
  Global Instance view_frag_sep_homomorphism :
    MonoidHomomorphism op op (≡) (@view_frag A B rel).
  Proof. by split; [split; try apply _|]. Qed.

  Lemma big_opL_view_frag {C} (g : nat → C → B) (l : list C) :
    (◯V [^op list] k↦x ∈ l, g k x) ≡ [^op list] k↦x ∈ l, ◯V (g k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_view_frag `{Countable K} {C} (g : K → C → B) (m : gmap K C) :
    (◯V [^op map] k↦x ∈ m, g k x) ≡ [^op map] k↦x ∈ m, ◯V (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_view_frag `{Countable C} (g : C → B) (X : gset C) :
    (◯V [^op set] x ∈ X, g x) ≡ [^op set] x ∈ X, ◯V (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_view_frag `{Countable C} (g : C → B) (X : gmultiset C) :
    (◯V [^op mset] x ∈ X, g x) ≡ [^op mset] x ∈ X, ◯V (g x).
  Proof. apply (big_opMS_commute _). Qed.

  (** Internalized properties *)
  Lemma view_both_validI {M} (relI : uPred M) q a b :
    (∀ n (x : M), relI n x ↔ rel n a b) →
    ✓ (●V{q} a ⋅ ◯V b) ⊣⊢ ✓ q ∧ relI.
  Proof.
    intros Hrel. uPred.unseal. split=> n x _ /=.
    by rewrite {1}/uPred_holds /= view_both_frac_validN -(Hrel _ x).
  Qed.
  Lemma view_auth_validI {M} (relI : uPred M) q a :
    (∀ n (x : M), relI n x ↔ rel n a ε) →
    ✓ (●V{q} a) ⊣⊢ ✓ q ∧ relI.
  Proof.
    intros. rewrite -(right_id ε op (●V{q} a)). by apply view_both_validI.
  Qed.
  Lemma view_frag_validI {M} b : ✓ (◯V b) ⊣⊢@{uPredI M} ✓ b.
  Proof. by uPred.unseal. Qed.

  (** Updates *)
  Lemma view_update a b a' b' :
    (∀ n bf, rel n a (b ⋅ bf) → rel n a' (b' ⋅ bf)) →
    ●V a ⋅ ◯V b ~~> ●V a' ⋅ ◯V b'.
  Proof.
    intros Hup; apply cmra_total_update=> n [[[q ag]|] bf] [/=].
    { by intros []%(exclusiveN_l _ _). }
    intros _ (a0 & <-%(inj to_agree) & Hrel). split; simpl; [done|].
    exists a'; split; [done|]. revert Hrel. rewrite !left_id. apply Hup.
  Qed.

  Lemma view_update_alloc a a' b' :
    (∀ n bf, rel n a bf → rel n a' (b' ⋅ bf)) →
    ●V a ~~> ●V a' ⋅ ◯V b'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a)).
    apply view_update=> n bf. rewrite left_id. apply Hup.
  Qed.
  Lemma view_update_dealloc a b a' :
    (∀ n bf, rel n a (b ⋅ bf) → rel n a' bf) →
    ●V a ⋅ ◯V b ~~> ●V a'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a')).
    apply view_update=> n bf. rewrite left_id. apply Hup.
  Qed.
  Lemma view_update_auth a a' b' :
    (∀ n bf, rel n a bf → rel n a' bf) → ●V a ~~> ●V a'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a)) -(right_id _ _ (●V a')).
    apply view_update=> n bf. rewrite !left_id. apply Hup.
  Qed.

  Lemma view_update_alloc_frac q a b :
    (∀ n bf, rel n a bf → rel n a (b ⋅ bf)) →
    ●V{q} a ~~> ●V{q} a ⋅ ◯V b.
  Proof.
    intros Hup. apply cmra_total_update=> n [[[p ag]|] bf] [/=].
    - intros ? (a0 & Hag & Hrel). split; simpl; [done|].
      exists a0; split; [done|]. revert Hrel.
      assert (to_agree a ≼{n} to_agree a0) as <-%to_agree_includedN.
      { by exists ag. }
      rewrite !left_id. apply Hup.
    - intros ? (a0 & <-%(inj to_agree) & Hrel). split; simpl; [done|].
      exists a; split; [done|]. revert Hrel. rewrite !left_id. apply Hup.
  Qed.

  Lemma view_local_update a b0 b1 a' b0' b1' :
    (b0, b1) ~l~> (b0', b1') → 
    (∀ n, view_rel_holds rel n a b0 → view_rel_holds rel n a' b0') →
    (●V a ⋅ ◯V b0, ●V a ⋅ ◯V b1) ~l~> (●V a' ⋅ ◯V b0', ●V a' ⋅ ◯V b1').
  Proof.
    rewrite !local_update_unital.
    move=> Hup Hrel n [[[q ag]|] bf] /view_both_validN Hrel' [/=].
    - rewrite right_id -Some_op -pair_op frac_op'=> /Some_dist_inj [/= H1q _].
      exfalso. apply (Qp_not_plus_q_ge_1 q). by rewrite -H1q.
    - rewrite !left_id=> _ Hb0.
      destruct (Hup n bf) as [? Hb0']; [by eauto using view_rel_validN..|].
      split; [apply view_both_validN; by auto|]. by rewrite -assoc Hb0'.
  Qed.
End cmra.

(** * Functor *)
(** Due to the dependent type [rel] in [view] we cannot actually define
instances of the functor structures [rFunctor] and [urFunctor]. Functors can
only be defined for instances of [view], like [auth]. To make it more convenient
to define functors for instances of [view], we define the map operation
[view_map] and a bunch of lemmas about it. *)
Definition view_map {A A' B B'}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') (x : view rel) : view rel' :=
  View (prod_map id (agree_map f) <$> view_auth_proj x) (g (view_frag_proj x)).
Lemma view_map_id {A B} {rel : nat → A → B → Prop} (x : view rel) :
  view_map id id x = x.
Proof. destruct x as [[[]|] ]; by rewrite // /view_map /= agree_map_id. Qed.
Lemma view_map_compose {A A' A'' B B' B''}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    {rel'' : nat → A'' → B'' → Prop}
    (f1 : A → A') (f2 : A' → A'') (g1 : B → B') (g2 : B' → B'') (x : view rel) :
  view_map (f2 ∘ f1) (g2 ∘ g1) x
  =@{view rel''} view_map f2 g2 (view_map (rel':=rel') f1 g1 x).
Proof. destruct x as [[[]|] ];  by rewrite // /view_map /= agree_map_compose. Qed.
Lemma view_map_ext  {A A' B B' : ofeT}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f1 f2 : A → A') (g1 g2 : B → B')
    `{!NonExpansive f1, !NonExpansive g1} (x : view rel) :
  (∀ a, f1 a ≡ f2 a) → (∀ b, g1 b ≡ g2 b) →
  view_map f1 g1 x ≡@{view rel'} view_map f2 g2 x.
Proof.
  intros. constructor; simpl; [|by auto].
  apply option_fmap_equiv_ext=> a; by rewrite /prod_map /= agree_map_ext.
Qed.
Instance view_map_ne {A A' B B' : ofeT}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') `{Hf : !NonExpansive f, Hg : !NonExpansive g} :
  NonExpansive (view_map (rel':=rel') (rel:=rel) f g).
Proof.
  intros n [o1 bf1] [o2 bf2] [??]; split; simpl in *; [|by apply Hg].
  apply option_fmap_ne; [|done]=> pag1 pag2 ?.
  apply prod_map_ne; [done| |done]. by apply agree_map_ne.
Qed.

Definition viewO_map {A A' B B' : ofeT}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A -n> A') (g : B -n> B') : viewO rel -n> viewO rel' :=
  OfeMor (view_map f g).
Lemma viewO_map_ne {A A' B B' : ofeT}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop} :
  NonExpansive2 (viewO_map (rel:=rel) (rel':=rel')).
Proof.
  intros n f f' Hf g g' Hg [[[p ag]|] bf]; split=> //=.
  do 2 f_equiv. by apply agreeO_map_ne.
Qed.

Lemma view_map_cmra_morphism {A A' B B'}
    {rel : view_rel A B} {rel' : view_rel A' B'}
    (f : A → A') (g : B → B') `{!NonExpansive f, !CmraMorphism g} :
  (∀ n a b, rel n a b → rel' n (f a) (g b)) →
  CmraMorphism (view_map (rel:=rel) (rel':=rel') f g).
Proof.
  intros Hrel. split.
  - apply _.
  - rewrite !view_validN_eq=> n [[[p ag]|] bf] /=;
      [|naive_solver eauto using cmra_morphism_validN].
    intros [? [a' [Hag ?]]]. split; [done|]. exists (f a'). split; [|by auto].
    by rewrite -agree_map_to_agree -Hag.
  - intros [o bf]. apply Some_proper; rewrite /view_map /=.
    f_equiv; by rewrite cmra_morphism_core.
  - intros [[[p1 ag1]|] bf1] [[[p2 ag2]|] bf2];
      try apply View_proper=> //=; by rewrite cmra_morphism_op.
Qed.
