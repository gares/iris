From iris.algebra Require Export cmra.
From iris.base_logic Require Import base_logic.
From iris Require Import options.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.

Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclBot : excl A.
Arguments Excl {_} _.
Arguments ExclBot {_}.

Instance: Params (@Excl) 1 := {}.
Instance: Params (@ExclBot) 1 := {}.

Notation excl' A := (option (excl A)).
Notation Excl' x := (Some (Excl x)).
Notation ExclBot' := (Some ExclBot).

Instance maybe_Excl {A} : Maybe (@Excl A) := λ x,
  match x with Excl a => Some a | _ => None end.

Section excl.
Context {A : ofeT}.
Implicit Types a b : A.
Implicit Types x y : excl A.

(* Cofe *)
Inductive excl_equiv : Equiv (excl A) :=
  | Excl_equiv a b : a ≡ b → Excl a ≡ Excl b
  | ExclBot_equiv : ExclBot ≡ ExclBot.
Existing Instance excl_equiv.
Inductive excl_dist : Dist (excl A) :=
  | Excl_dist a b n : a ≡{n}≡ b → Excl a ≡{n}≡ Excl b
  | ExclBot_dist n : ExclBot ≡{n}≡ ExclBot.
Existing Instance excl_dist.

Global Instance Excl_ne : NonExpansive (@Excl A).
Proof. by constructor. Qed.
Global Instance Excl_proper : Proper ((≡) ==> (≡)) (@Excl A).
Proof. by constructor. Qed.
Global Instance Excl_inj : Inj (≡) (≡) (@Excl A).
Proof. by inversion_clear 1. Qed.
Global Instance Excl_dist_inj n : Inj (dist n) (dist n) (@Excl A).
Proof. by inversion_clear 1. Qed.

Definition excl_ofe_mixin : OfeMixin (excl A).
Proof.
  apply (iso_ofe_mixin (maybe Excl)).
  - by intros [a|] [b|]; split; inversion_clear 1; constructor.
  - by intros n [a|] [b|]; split; inversion_clear 1; constructor.
Qed.
Canonical Structure exclO : ofeT := OfeT (excl A) excl_ofe_mixin.

Global Instance excl_cofe `{!Cofe A} : Cofe exclO.
Proof.
  apply (iso_cofe (from_option Excl ExclBot) (maybe Excl)).
  - by intros n [a|] [b|]; split; inversion_clear 1; constructor.
  - by intros []; constructor.
Qed.

Global Instance excl_ofe_discrete : OfeDiscrete A → OfeDiscrete exclO.
Proof. by inversion_clear 2; constructor; apply (discrete _). Qed.
Global Instance excl_leibniz : LeibnizEquiv A → LeibnizEquiv (excl A).
Proof. by destruct 2; f_equal; apply leibniz_equiv. Qed.

Global Instance Excl_discrete a : Discrete a → Discrete (Excl a).
Proof. by inversion_clear 2; constructor; apply (discrete _). Qed.
Global Instance ExclBot_discrete : Discrete (@ExclBot A).
Proof. by inversion_clear 1; constructor. Qed.

(* CMRA *)
Instance excl_valid : Valid (excl A) := λ x,
  match x with Excl _ => True | ExclBot => False end.
Instance excl_validN : ValidN (excl A) := λ n x,
  match x with Excl _ => True | ExclBot => False end.
Instance excl_pcore : PCore (excl A) := λ _, None.
Instance excl_op : Op (excl A) := λ x y, ExclBot.

Lemma excl_cmra_mixin : CmraMixin (excl A).
Proof.
  split; try discriminate.
  - by intros n []; destruct 1; constructor.
  - by destruct 1; intros ?.
  - intros x; split. done. by move=> /(_ 0).
  - intros n [?|]; simpl; auto with lia.
  - by intros [?|] [?|] [?|]; constructor.
  - by intros [?|] [?|]; constructor.
  - by intros n [?|] [?|].
  - intros n x [?|] [?|] ? Hx; eexists _, _; inversion_clear Hx; eauto.
Qed.
Canonical Structure exclR := CmraT (excl A) excl_cmra_mixin.

Global Instance excl_cmra_discrete : OfeDiscrete A → CmraDiscrete exclR.
Proof. split. apply _. by intros []. Qed.

(** Internalized properties *)
Lemma excl_equivI {M} x y :
  x ≡ y ⊣⊢@{uPredI M} match x, y with
                      | Excl a, Excl b => a ≡ b
                      | ExclBot, ExclBot => True
                      | _, _ => False
                      end.
Proof.
  uPred.unseal. do 2 split. by destruct 1. by destruct x, y; try constructor.
Qed.
Lemma excl_validI {M} x :
  ✓ x ⊣⊢@{uPredI M} if x is ExclBot then False else True.
Proof. uPred.unseal. by destruct x. Qed.

(** Exclusive *)
Global Instance excl_exclusive x : Exclusive x.
Proof. by destruct x; intros n []. Qed.

(** Option excl *)
Lemma excl_validN_inv_l n mx a : ✓{n} (Excl' a ⋅ mx) → mx = None.
Proof. by destruct mx. Qed.
Lemma excl_validN_inv_r n mx a : ✓{n} (mx ⋅ Excl' a) → mx = None.
Proof. by destruct mx. Qed.

Lemma Excl_includedN n a b  : Excl' a ≼{n} Excl' b ↔ a ≡{n}≡ b.
Proof.
  split; [|by intros ->]. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb.
Qed.
Lemma Excl_included a b : Excl' a ≼ Excl' b ↔ a ≡ b.
Proof.
  split; [|by intros ->]. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb.
Qed.
End excl.

Arguments exclO : clear implicits.
Arguments exclR : clear implicits.

(* Functor *)
Definition excl_map {A B} (f : A → B) (x : excl A) : excl B :=
  match x with Excl a => Excl (f a) | ExclBot => ExclBot end.
Lemma excl_map_id {A} (x : excl A) : excl_map id x = x.
Proof. by destruct x. Qed.
Lemma excl_map_compose {A B C} (f : A → B) (g : B → C) (x : excl A) :
  excl_map (g ∘ f) x = excl_map g (excl_map f x).
Proof. by destruct x. Qed.
Lemma excl_map_ext {A B : ofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → excl_map f x ≡ excl_map g x.
Proof. by destruct x; constructor. Qed.
Instance excl_map_ne {A B : ofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@excl_map A B).
Proof. by intros f f' Hf; destruct 1; constructor; apply Hf. Qed.
Instance excl_map_cmra_morphism {A B : ofeT} (f : A → B) :
  NonExpansive f → CmraMorphism (excl_map f).
Proof. split; try done; try apply _. by intros n [a|]. Qed.
Definition exclO_map {A B} (f : A -n> B) : exclO A -n> exclO B :=
  OfeMor (excl_map f).
Instance exclO_map_ne A B : NonExpansive (@exclO_map A B).
Proof. by intros n f f' Hf []; constructor; apply Hf. Qed.

Program Definition exclRF (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := (exclR (oFunctor_car F A B));
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := exclO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n x1 x2 ??. by apply exclO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x; simpl. rewrite -{2}(excl_map_id x).
  apply excl_map_ext=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl. rewrite -excl_map_compose.
  apply excl_map_ext=>y; apply oFunctor_map_compose.
Qed.

Instance exclRF_contractive F :
  oFunctorContractive F → rFunctorContractive (exclRF F).
Proof.
  intros A1 ? A2 ? B1 ? B2 ? n x1 x2 ??. by apply exclO_map_ne, oFunctor_map_contractive.
Qed.
