From iris.proofmode Require Import tactics.
From iris.algebra Require Export frac agree local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.base_logic Require Import base_logic.
From iris Require Import options.

(** Authoritative CMRA with fractional authoritative parts. [auth] has 3 types
  of elements: the fractional authoritative `●{q} a`, the full authoritative
  `● a ≡ ●{1} a`, and the non-authoritative `◯ a`. Updates are only possible
  with the full authoritative element `● a`, while fractional authoritative
  elements have agreement: `✓ (●{p} a ⋅ ●{q} b) ⇒ a ≡ b`.
*)

Record auth (A : Type) :=
  Auth { auth_auth_proj : option (frac * agree A) ; auth_frag_proj : A }.
Add Printing Constructor auth.
Arguments Auth {_} _ _.
Arguments auth_auth_proj {_} _.
Arguments auth_frag_proj {_} _.
Instance: Params (@Auth) 1 := {}.
Instance: Params (@auth_auth_proj) 1 := {}.
Instance: Params (@auth_frag_proj) 1 := {}.

Definition auth_frag {A: ucmraT} (a: A) : auth A := Auth None a.
Definition auth_auth {A: ucmraT} (q: Qp) (a: A) : auth A :=
  Auth (Some (q, to_agree a)) ε.

Typeclasses Opaque auth_auth auth_frag.

Instance: Params (@auth_frag) 1 := {}.
Instance: Params (@auth_auth) 1 := {}.

Notation "◯ a" := (auth_frag a) (at level 20).
Notation "●{ q } a" := (auth_auth q a) (at level 20, format "●{ q }  a").
Notation "● a" := (auth_auth 1 a) (at level 20).

(* Ofe *)
Section ofe.
Context {A : ofeT}.
Implicit Types a : option (frac * agree A).
Implicit Types b : A.
Implicit Types x y : auth A.

Instance auth_equiv : Equiv (auth A) := λ x y,
  auth_auth_proj x ≡ auth_auth_proj y ∧ auth_frag_proj x ≡ auth_frag_proj y.
Instance auth_dist : Dist (auth A) := λ n x y,
  auth_auth_proj x ≡{n}≡ auth_auth_proj y ∧
  auth_frag_proj x ≡{n}≡ auth_frag_proj y.

Global Instance Auth_ne : NonExpansive2 (@Auth A).
Proof. by split. Qed.
Global Instance Auth_proper : Proper ((≡) ==> (≡) ==> (≡)) (@Auth A).
Proof. by split. Qed.
Global Instance auth_auth_proj_ne: NonExpansive (@auth_auth_proj A).
Proof. by destruct 1. Qed.
Global Instance auth_auth_proj_proper : Proper ((≡) ==> (≡)) (@auth_auth_proj A).
Proof. by destruct 1. Qed.
Global Instance auth_frag_proj_ne : NonExpansive (@auth_frag_proj A).
Proof. by destruct 1. Qed.
Global Instance auth_frag_proj_proper : Proper ((≡) ==> (≡)) (@auth_frag_proj A).
Proof. by destruct 1. Qed.

Definition auth_ofe_mixin : OfeMixin (auth A).
Proof. by apply (iso_ofe_mixin (λ x, (auth_auth_proj x, auth_frag_proj x))). Qed.
Canonical Structure authO := OfeT (auth A) auth_ofe_mixin.

Global Instance Auth_discrete a b :
  Discrete a → Discrete b → Discrete (Auth a b).
Proof. by intros ?? [??] [??]; split; apply: discrete. Qed.
Global Instance auth_ofe_discrete : OfeDiscrete A → OfeDiscrete authO.
Proof. intros ? [??]; apply _. Qed.

(** Internalized properties *)
Lemma auth_equivI {M} x y :
  x ≡ y ⊣⊢@{uPredI M} auth_auth_proj x ≡ auth_auth_proj y ∧ auth_frag_proj x ≡ auth_frag_proj y.
Proof. by uPred.unseal. Qed.
End ofe.

Arguments authO : clear implicits.

(* Camera *)
Section cmra.
Context {A : ucmraT}.
Implicit Types a b : A.
Implicit Types x y : auth A.

Global Instance auth_frag_ne: NonExpansive (@auth_frag A).
Proof. done. Qed.
Global Instance auth_frag_proper : Proper ((≡) ==> (≡)) (@auth_frag A).
Proof. done. Qed.
Global Instance auth_auth_ne q : NonExpansive (@auth_auth A q).
Proof. solve_proper. Qed.
Global Instance auth_auth_proper : Proper ((≡) ==> (≡) ==> (≡)) (@auth_auth A).
Proof. solve_proper. Qed.
Global Instance auth_auth_discrete q a :
  Discrete a → Discrete (ε : A) → Discrete (●{q} a).
Proof. intros. apply Auth_discrete; apply _. Qed.
Global Instance auth_frag_discrete a : Discrete a → Discrete (◯ a).
Proof. intros. apply Auth_discrete; apply _. Qed.

Instance auth_valid : Valid (auth A) := λ x,
  match auth_auth_proj x with
  | Some (q, ag) =>
      ✓ q ∧ (∀ n, ∃ a, ag ≡{n}≡ to_agree a ∧ auth_frag_proj x ≼{n} a ∧ ✓{n} a)
  | None => ✓ auth_frag_proj x
  end.
Instance auth_validN : ValidN (auth A) := λ n x,
  match auth_auth_proj x with
  | Some (q, ag) =>
      ✓{n} q ∧ ∃ a, ag ≡{n}≡ to_agree a ∧ auth_frag_proj x ≼{n} a ∧ ✓{n} a
  | None => ✓{n} auth_frag_proj x
  end.
Instance auth_pcore : PCore (auth A) := λ x,
  Some (Auth (core (auth_auth_proj x)) (core (auth_frag_proj x))).
Instance auth_op : Op (auth A) := λ x y,
  Auth (auth_auth_proj x ⋅ auth_auth_proj y) (auth_frag_proj x ⋅ auth_frag_proj y).

Definition auth_valid_eq :
  valid = λ x, match auth_auth_proj x with
               | Some (q, ag) => ✓ q ∧ (∀ n, ∃ a, ag ≡{n}≡ to_agree a ∧ auth_frag_proj x ≼{n} a ∧ ✓{n} a)
               | None => ✓ auth_frag_proj x
               end := eq_refl _.
Definition auth_validN_eq :
  validN = λ n x, match auth_auth_proj x with
                  | Some (q, ag) => ✓{n} q ∧ ∃ a, ag ≡{n}≡ to_agree a ∧ auth_frag_proj x ≼{n} a ∧ ✓{n} a
                  | None => ✓{n} auth_frag_proj x
                  end := eq_refl _.

Lemma auth_included (x y : auth A) :
  x ≼ y ↔
  auth_auth_proj x ≼ auth_auth_proj y ∧ auth_frag_proj x ≼ auth_frag_proj y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.

Lemma auth_auth_proj_validN n x : ✓{n} x → ✓{n} auth_auth_proj x.
Proof. destruct x as [[[]|]]; [by intros (? & ? & -> & ?)|done]. Qed.
Lemma auth_frag_proj_validN n x : ✓{n} x → ✓{n} auth_frag_proj x.
Proof.
  rewrite auth_validN_eq.
  destruct x as [[[]|]]; [|done]. naive_solver eauto using cmra_validN_includedN.
Qed.
Lemma auth_auth_proj_valid x : ✓ x → ✓ auth_auth_proj x.
Proof.
  destruct x as [[[]|]]; [intros [? H]|done]. split; [done|].
  intros n. by destruct (H n) as [? [-> [? ?]]].
Qed.
Lemma auth_frag_proj_valid x : ✓ x → ✓ auth_frag_proj x.
Proof.
  destruct x as [[[]|]]; [intros [? H]|done]. apply cmra_valid_validN.
  intros n. destruct (H n) as [? [? [? ?]]].
  naive_solver eauto using cmra_validN_includedN.
Qed.

Lemma auth_frag_validN n a : ✓{n} (◯ a) ↔ ✓{n} a.
Proof. done. Qed.
Lemma auth_auth_frac_validN n q a :
  ✓{n} (●{q} a) ↔ ✓{n} q ∧ ✓{n} a.
Proof.
  rewrite auth_validN_eq /=. apply and_iff_compat_l. split.
  - by intros [?[->%(inj to_agree) []]].
  - naive_solver eauto using ucmra_unit_leastN.
Qed.
Lemma auth_auth_validN n a : ✓{n} a ↔ ✓{n} (● a).
Proof.
  rewrite auth_auth_frac_validN -cmra_discrete_valid_iff frac_valid'. naive_solver.
Qed.
Lemma auth_both_frac_validN n q a b :
  ✓{n} (●{q} a ⋅ ◯ b) ↔ ✓{n} q ∧ b ≼{n} a ∧ ✓{n} a.
Proof.
  rewrite auth_validN_eq /=. apply and_iff_compat_l.
  setoid_rewrite (left_id _ _ b). split.
  - by intros [?[->%(inj to_agree)]].
  - naive_solver.
Qed.
Lemma auth_both_validN n a b : ✓{n} (● a ⋅ ◯ b) ↔ b ≼{n} a ∧ ✓{n} a.
Proof.
  rewrite auth_both_frac_validN -cmra_discrete_valid_iff frac_valid'. naive_solver.
Qed.

Lemma auth_frag_valid a : ✓ (◯ a) ↔ ✓ a.
Proof. done. Qed.
Lemma auth_auth_frac_valid q a : ✓ (●{q} a) ↔ ✓ q ∧ ✓ a.
Proof.
  rewrite auth_valid_eq /=. apply and_iff_compat_l. split.
  - intros H'. apply cmra_valid_validN. intros n.
    by destruct (H' n) as [? [->%(inj to_agree) [??]]].
  - intros. exists a. split; [done|].
    split; by [apply ucmra_unit_leastN|apply cmra_valid_validN].
Qed.
Lemma auth_auth_valid a : ✓ (● a) ↔ ✓ a.
Proof. rewrite auth_auth_frac_valid frac_valid'. naive_solver. Qed.

(* The reverse direction of the two lemmas below only holds if the camera is
discrete. *)
Lemma auth_both_frac_valid_2 q a b : ✓ q → ✓ a → b ≼ a → ✓ (●{q} a ⋅ ◯ b).
Proof.
  intros Val1 Val2 Incl. rewrite auth_valid_eq /=. split; [done|].
  intros n. exists a. split; [done|]. rewrite left_id.
  split; by [apply cmra_included_includedN|apply cmra_valid_validN].
Qed.
Lemma auth_both_valid_2 a b : ✓ a → b ≼ a → ✓ (● a ⋅ ◯ b).
Proof. intros ??. by apply auth_both_frac_valid_2. Qed.

Lemma auth_valid_discrete `{!CmraDiscrete A} x :
  ✓ x ↔ match auth_auth_proj x with
        | Some (q, ag) => ✓ q ∧ ∃ a, ag ≡ to_agree a ∧ auth_frag_proj x ≼ a ∧ ✓ a
        | None => ✓ auth_frag_proj x
        end.
Proof.
  rewrite auth_valid_eq. destruct x as [[[??]|] ?]; simpl; [|done].
  setoid_rewrite <-cmra_discrete_included_iff.
  setoid_rewrite <-(discrete_iff _ a).
  setoid_rewrite <-cmra_discrete_valid_iff. naive_solver eauto using O.
Qed.
Lemma auth_both_frac_valid `{!CmraDiscrete A} q a b :
  ✓ (●{q} a ⋅ ◯ b) ↔ ✓ q ∧ b ≼ a ∧ ✓ a.
Proof.
  rewrite auth_valid_discrete /=. apply and_iff_compat_l.
  setoid_rewrite (left_id _ _ b). split.
  - by intros [?[->%(inj to_agree)]].
  - naive_solver.
Qed.
Lemma auth_both_valid `{!CmraDiscrete A} a b : ✓ (● a ⋅ ◯ b) ↔ b ≼ a ∧ ✓ a.
Proof. rewrite auth_both_frac_valid frac_valid'. naive_solver. Qed.

Lemma auth_cmra_mixin : CmraMixin (auth A).
Proof.
  apply (iso_cmra_mixin_restrict (λ x : option (frac * agree A) * A, Auth x.1 x.2)
    (λ x, (auth_auth_proj x, auth_frag_proj x))); try done.
  - intros [x b]. by rewrite /= pair_pcore !cmra_pcore_core.
  - intros n [[[q aa]|] b]; rewrite /= auth_validN_eq /=; last done.
    intros (?&a&->&?&?). split; simpl; by eauto using cmra_validN_includedN.
  - rewrite auth_validN_eq.
    intros n [x1 b1] [x2 b2] [Hx ?]; simpl in *;
      destruct Hx as [[q1 aa1] [q2 aa2] [??]|]; intros ?; by ofe_subst.
  - rewrite auth_valid_eq auth_validN_eq.
    intros [[[q aa]|] b]; rewrite /= cmra_valid_validN; naive_solver.
  - rewrite auth_validN_eq. intros n [[[q aa]|] b];
      naive_solver eauto using dist_S, cmra_includedN_S, cmra_validN_S.
  - assert (∀ n (a b1 b2 : A), b1 ⋅ b2 ≼{n} a → b1 ≼{n} a).
    { intros n a b1 b2 <-; apply cmra_includedN_l. }
    rewrite auth_validN_eq. intros n [[[q1 a1]|] b1] [[[q2 a2]|] b2]; simpl;
      [|naive_solver eauto using cmra_validN_op_l, cmra_validN_includedN..].
    intros [? [a [Ha12a [? Valid]]]].
    assert (a1 ≡{n}≡ a2) as Ha12 by (apply agree_op_invN; by rewrite Ha12a).
    split; [naive_solver eauto using cmra_validN_op_l|].
    exists a. rewrite -Ha12a -Ha12 agree_idemp. naive_solver.
Qed.
Canonical Structure authR := CmraT (auth A) auth_cmra_mixin.

Global Instance auth_cmra_discrete : CmraDiscrete A → CmraDiscrete authR.
Proof.
  split; first apply _.
  intros [[[]|] ?]; rewrite auth_valid_eq auth_validN_eq /=; auto.
  - setoid_rewrite <-cmra_discrete_included_iff.
    rewrite -cmra_discrete_valid_iff.
    setoid_rewrite <-cmra_discrete_valid_iff.
    setoid_rewrite <-(discrete_iff _ a). tauto.
  - by rewrite -cmra_discrete_valid_iff.
Qed.

Instance auth_empty : Unit (auth A) := Auth ε ε.
Lemma auth_ucmra_mixin : UcmraMixin (auth A).
Proof.
  split; simpl.
  - rewrite auth_valid_eq /=. apply ucmra_unit_valid.
  - by intros x; constructor; rewrite /= left_id.
  - do 2 constructor; [done| apply (core_id_core _)].
Qed.
Canonical Structure authUR := UcmraT (auth A) auth_ucmra_mixin.

Global Instance auth_frag_core_id a : CoreId a → CoreId (◯ a).
Proof. do 2 constructor; simpl; auto. by apply core_id_core. Qed.

Lemma auth_frag_op a b : ◯ (a ⋅ b) = ◯ a ⋅ ◯ b.
Proof. done. Qed.
Lemma auth_frag_mono a b : a ≼ b → ◯ a ≼ ◯ b.
Proof. intros [c ->]. rewrite auth_frag_op. apply cmra_included_l. Qed.
Lemma auth_frag_core a : core (◯ a) = ◯ (core a).
Proof. done. Qed.

Global Instance auth_frag_sep_homomorphism :
  MonoidHomomorphism op op (≡) (@auth_frag A).
Proof. by split; [split; try apply _|]. Qed.

Lemma big_opL_auth_frag {B} (g : nat → B → A) (l : list B) :
  (◯ [^op list] k↦x ∈ l, g k x) ≡ [^op list] k↦x ∈ l, ◯ (g k x).
Proof. apply (big_opL_commute _). Qed.
Lemma big_opM_auth_frag `{Countable K} {B} (g : K → B → A) (m : gmap K B) :
  (◯ [^op map] k↦x ∈ m, g k x) ≡ [^op map] k↦x ∈ m, ◯ (g k x).
Proof. apply (big_opM_commute _). Qed.
Lemma big_opS_auth_frag `{Countable B} (g : B → A) (X : gset B) :
  (◯ [^op set] x ∈ X, g x) ≡ [^op set] x ∈ X, ◯ (g x).
Proof. apply (big_opS_commute _). Qed.
Lemma big_opMS_auth_frag `{Countable B} (g : B → A) (X : gmultiset B) :
  (◯ [^op mset] x ∈ X, g x) ≡ [^op mset] x ∈ X, ◯ (g x).
Proof. apply (big_opMS_commute _). Qed.

Lemma auth_both_op q a b : Auth (Some (q,to_agree a)) b ≡ ●{q} a ⋅ ◯ b.
Proof. by rewrite /op /auth_op /= left_id. Qed.

Lemma auth_auth_frac_op p q a : ●{p + q} a ≡ ●{p} a ⋅ ●{q} a.
Proof.
  intros; split; simpl; last by rewrite left_id.
  by rewrite -Some_op -pair_op agree_idemp.
Qed.
Lemma auth_auth_frac_op_invN n p a q b : ✓{n} (●{p} a ⋅ ●{q} b) → a ≡{n}≡ b.
Proof.
  rewrite /op /auth_op /= left_id -Some_op -pair_op auth_validN_eq /=.
  intros (?&?& Eq &?&?). apply (inj to_agree), agree_op_invN. by rewrite Eq.
Qed.
Lemma auth_auth_frac_op_inv p a q b : ✓ (●{p} a ⋅ ●{q} b) → a ≡ b.
Proof.
  intros ?. apply equiv_dist. intros n.
  by eapply auth_auth_frac_op_invN, cmra_valid_validN.
Qed.
Lemma auth_auth_frac_op_inv_L `{!LeibnizEquiv A} q a p b :
  ✓ (●{p} a ⋅ ●{q} b) → a = b.
Proof. by intros ?%auth_auth_frac_op_inv%leibniz_equiv. Qed.

(** Internalized properties *)
Lemma auth_validI {M} x :
  ✓ x ⊣⊢@{uPredI M} match auth_auth_proj x with
                    | Some (q, ag) => ✓ q ∧
                      ∃ a, ag ≡ to_agree a ∧ (∃ b, a ≡ auth_frag_proj x ⋅ b) ∧ ✓ a
                    | None => ✓ auth_frag_proj x
                    end.
Proof. uPred.unseal. by destruct x as [[[]|]]. Qed.
Lemma auth_frag_validI {M} (a : A):
  ✓ (◯ a) ⊣⊢@{uPredI M} ✓ a.
Proof. by rewrite auth_validI. Qed.

Lemma auth_both_validI {M} q (a b: A) :
  ✓ (●{q} a ⋅ ◯ b) ⊣⊢@{uPredI M} ✓ q ∧ (∃ c, a ≡ b ⋅ c) ∧ ✓ a.
Proof.
  rewrite -auth_both_op auth_validI /=. apply bi.and_proper; [done|].
  setoid_rewrite agree_equivI. iSplit.
  - iDestruct 1 as (a') "[#Eq [H V]]". iDestruct "H" as (b') "H".
    iRewrite -"Eq" in "H". iRewrite -"Eq" in "V". auto.
  - iDestruct 1 as "[H V]". iExists a. auto.
Qed.
Lemma auth_auth_validI {M} q (a b: A) :
  ✓ (●{q} a) ⊣⊢@{uPredI M} ✓ q ∧ ✓ a.
Proof.
  rewrite auth_validI /=. apply bi.and_proper; [done|].
  setoid_rewrite agree_equivI. iSplit.
  - iDestruct 1 as (a') "[Eq [_ V]]". by iRewrite -"Eq" in "V".
  - iIntros "V". iExists a. iSplit; [done|]. iSplit; [|done]. iExists a.
    by rewrite left_id.
Qed.

Lemma auth_update a b a' b' :
  (a,b) ~l~> (a',b') → ● a ⋅ ◯ b ~~> ● a' ⋅ ◯ b'.
Proof.
  intros Hup; apply cmra_total_update.
  move=> n [[qa|] bf1] [/= Hq [a0 [Haa0 [[bf2 Ha] Ha0]]]]; do 2 red; simpl in *.
  { by apply (exclusiveN_l _ _) in Hq. }
  split; [done|]. apply (inj to_agree) in Haa0.
  move: Ha; rewrite !left_id -assoc=> Ha.
  destruct (Hup n (Some (bf1 ⋅ bf2))); [by rewrite Haa0..|]; simpl in *.
  exists a'. split_and!; [done| |done].
  exists bf2. by rewrite left_id -assoc.
Qed.

Lemma auth_update_alloc a a' b' : (a,ε) ~l~> (a',b') → ● a ~~> ● a' ⋅ ◯ b'.
Proof. intros. rewrite -(right_id _ _ (● a)). by apply auth_update. Qed.

Lemma auth_update_auth a a' b' : (a,ε) ~l~> (a',b') → ● a ~~> ● a'.
Proof.
  intros. etrans; first exact: auth_update_alloc.
  exact: cmra_update_op_l.
Qed.

Lemma auth_update_core_id q a b `{!CoreId b} :
  b ≼ a → ●{q} a ~~> ●{q} a ⋅ ◯ b.
Proof.
  intros Ha%(core_id_extract _ _). apply cmra_total_update.
  move=> n [[[q' ag]|] bf1] [Hq [a0 [Haa0 [Hbf1 Ha0]]]]; simpl in *.
  + split; simpl; [done|]. exists a0. split_and!; [done| |done].
    assert (a ≡{n}≡ a0) as Haa0' by (apply to_agree_includedN; by exists ag).
    rewrite -Haa0' Ha Haa0' -assoc (comm _ b) assoc. by apply cmra_monoN_r.
  + split; simpl; [done|]. exists a0. split_and!; [done| |done].
    apply (inj to_agree) in Haa0.
    rewrite -Haa0 Ha Haa0 -assoc (comm _ b) assoc. by apply cmra_monoN_r.
Qed.

Lemma auth_update_dealloc a b a' : (a,b) ~l~> (a',ε) → ● a ⋅ ◯ b ~~> ● a'.
Proof. intros. rewrite -(right_id _ _ (● a')). by apply auth_update. Qed.

Lemma auth_local_update (a b0 b1 a' b0' b1': A) :
  (b0, b1) ~l~> (b0', b1') → b0' ≼ a' → ✓ a' →
  (● a ⋅ ◯ b0, ● a ⋅ ◯ b1) ~l~> (● a' ⋅ ◯ b0', ● a' ⋅ ◯ b1').
Proof.
  rewrite !local_update_unital=> Hup ? ? n /=.
    move=> [[[qc ac]|] bc] /auth_both_validN [Le Val] [] /=.
  - move => Ha. exfalso. move : Ha. rewrite right_id -Some_op -pair_op frac_op'.
    move => /Some_dist_inj [/= Eq _].
    apply (Qp_not_plus_q_ge_1 qc). by rewrite -Eq.
  - move => _. rewrite !left_id=> ?.
    destruct (Hup n bc) as [Hval' Heq]; eauto using cmra_validN_includedN.
    rewrite -!auth_both_op auth_validN_eq /=.
    split_and!; [done| |done]. exists a'.
    split_and!; [done|by apply cmra_included_includedN|by apply cmra_valid_validN].
Qed.
End cmra.

Arguments authR : clear implicits.
Arguments authUR : clear implicits.

(* Proof mode class instances *)
Instance is_op_auth_frag {A : ucmraT} (a b1 b2 : A) :
  IsOp a b1 b2 → IsOp' (◯ a) (◯ b1) (◯ b2).
Proof. done. Qed.
Instance is_op_auth_auth_frac {A : ucmraT} (q q1 q2 : frac) (a : A) :
  IsOp q q1 q2 → IsOp' (●{q} a) (●{q1} a) (●{q2} a).
Proof. rewrite /IsOp' /IsOp => ->. by rewrite -auth_auth_frac_op. Qed.

(* Functor *)
Definition auth_map {A B} (f : A → B) (x : auth A) : auth B :=
  Auth (prod_map id (agree_map f) <$> auth_auth_proj x) (f (auth_frag_proj x)).
Lemma auth_map_id {A} (x : auth A) : auth_map id x = x.
Proof. destruct x as [[[]|] ]; by rewrite // /auth_map /= agree_map_id. Qed.
Lemma auth_map_compose {A B C} (f : A → B) (g : B → C) (x : auth A) :
  auth_map (g ∘ f) x = auth_map g (auth_map f x).
Proof. destruct x as [[[]|] ];  by rewrite // /auth_map /= agree_map_compose. Qed.
Lemma auth_map_ext {A B : ofeT} (f g : A → B) `{!NonExpansive f} x :
  (∀ x, f x ≡ g x) → auth_map f x ≡ auth_map g x.
Proof.
  constructor; simpl; auto.
  apply option_fmap_equiv_ext=> a; by rewrite /prod_map /= agree_map_ext.
Qed.
Instance auth_map_ne {A B : ofeT} (f : A -> B) `{Hf : !NonExpansive f} :
  NonExpansive (auth_map f).
Proof.
  intros n [??] [??] [??]; split; simpl in *; [|by apply Hf].
  apply option_fmap_ne; [|done]=> x y ?. apply prod_map_ne; [done| |done].
  by apply agree_map_ne.
Qed.
Instance auth_map_cmra_morphism {A B : ucmraT} (f : A → B) :
  CmraMorphism f → CmraMorphism (auth_map f).
Proof.
  split; try apply _.
  - intros n [[[??]|] b]; rewrite !auth_validN_eq;
      [|naive_solver eauto using cmra_morphism_monotoneN, cmra_morphism_validN].
    intros [? [a' [Eq [? ?]]]]. split; [done|]. exists (f a').
    rewrite -agree_map_to_agree -Eq.
    naive_solver eauto using cmra_morphism_monotoneN, cmra_morphism_validN.
  - intros [??]. apply Some_proper; rewrite /auth_map /=.
    by f_equiv; rewrite /= cmra_morphism_core.
  - intros [[[??]|]?] [[[??]|]?]; try apply Auth_proper=>//=; by rewrite cmra_morphism_op.
Qed.
Definition authO_map {A B} (f : A -n> B) : authO A -n> authO B :=
  OfeMor (auth_map f).
Lemma authO_map_ne A B : NonExpansive (@authO_map A B).
Proof. intros n f f' Hf [[[]|] ]; repeat constructor; try naive_solver;
  apply agreeO_map_ne; auto. Qed.

Program Definition authURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := authUR (urFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg := authO_map (urFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply authO_map_ne, urFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(auth_map_id x).
  apply (auth_map_ext _ _)=>y; apply urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -auth_map_compose.
  apply (auth_map_ext _ _)=>y; apply urFunctor_map_compose.
Qed.

Instance authURF_contractive F :
  urFunctorContractive F → urFunctorContractive (authURF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply authO_map_ne, urFunctor_map_contractive.
Qed.

Definition authRF (F : urFunctor) :=
  urFunctor_to_rFunctor (authURF F).
