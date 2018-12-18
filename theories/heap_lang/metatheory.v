From iris.heap_lang Require Export lang.
From stdpp Require Import gmap.

(* This file contains some metatheory about the heap_lang language,
  which is not needed for verifying programs. *)

(* Closed expressions and values. *)
Fixpoint is_closed_expr (X : list string) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr (f :b: x :b: X) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2
  | ResolveProph e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | NewProph => true
  end
with is_closed_val (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr (f :b: x :b: []) e
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v | InjRV v => is_closed_val v
  end.

Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed_expr [] e → is_closed_expr X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x v :
  is_closed_val v → is_closed_expr (x :: X) e → is_closed_expr X (subst x v e).
Proof.
  intros Hv. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_subst' X e x v :
  is_closed_val v → is_closed_expr (x :b: X) e → is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(* Substitution *)
Lemma subst_is_closed X e x es : is_closed_expr X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=; rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x v : is_closed_expr [] e → subst x v e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst_ne' e x y v v' :
  x ≠ y → subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x v :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x v (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x v :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x v (Rec f y e) = Rec f y (subst' x v e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

(* The stepping relation preserves closedness *)
Lemma head_step_is_closed e1 σ1 obs e2 σ2 es :
  is_closed_expr [] e1 →
  map_Forall (λ _ v, is_closed_val v) σ1.(heap) →
  head_step e1 σ1 obs e2 σ2 es →

  is_closed_expr [] e2 ∧ Forall (is_closed_expr []) es ∧
  map_Forall (λ _ v, is_closed_val v) σ2.(heap).
Proof.
  intros Cl1 Clσ1 STEP.
  destruct STEP; simpl in *; split_and!;
    try apply map_Forall_insert_2; try by naive_solver.
  - subst. repeat apply is_closed_subst'; naive_solver.
  - unfold un_op_eval in *. repeat case_match; naive_solver.
  - unfold bin_op_eval, bin_op_eval_bool in *. repeat case_match; naive_solver.
Qed.

(* Parallel substitution with maps of values indexed by strings *)
Definition binder_delete {A} (x : binder) (vs : gmap string A) : gmap string A :=
  if x is BNamed x' then delete x' vs else vs.
Definition binder_insert {A} (x : binder) (v : A) (vs : gmap string A) : gmap string A :=
  if x is BNamed x' then <[x':=v]>vs else vs.

Lemma binder_insert_fmap {A B : Type} (f : A → B) (x : A) b vs :
  f <$> binder_insert b x vs = binder_insert b (f x) (f <$> vs).
Proof. destruct b; rewrite ?fmap_insert //. Qed.

Fixpoint subst_map (vs : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e => Fst (subst_map vs e)
  | Snd e => Snd (subst_map vs e)
  | InjL e => InjL (subst_map vs e)
  | InjR e => InjR (subst_map vs e)
  | Case e0 e1 e2 => Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Fork e => Fork (subst_map vs e)
  | Alloc e => Alloc (subst_map vs e)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  | CAS e0 e1 e2 => CAS (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | FAA e1 e2 => FAA (subst_map vs e1) (subst_map vs e2)
  | NewProph => NewProph
  | ResolveProph e1 e2 => ResolveProph (subst_map vs e1) (subst_map vs e2)
  end.

Lemma subst_map_empty e : subst_map ∅ e = e.
Proof.
  assert (∀ x, binder_delete x (∅:gmap _ val) = ∅) as Hdel.
  { intros [|x]; by rewrite /= ?delete_empty. }
  induction e; simplify_map_eq; rewrite ?Hdel; auto with f_equal.
Qed.
Lemma subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. assert (∀ (y : binder) (vs : gmap _ val), y ≠ BNamed x →
    binder_delete y (<[x:=v]> vs) = <[x:=v]> (binder_delete y vs)) as Hins.
  { intros [|y] vs ?; rewrite /= ?delete_insert_ne //; congruence. }
  assert (∀ (y : binder) (vs : gmap _ val),
    binder_delete y (delete x vs) = delete x (binder_delete y vs)) as Hdel.
  { by intros [|y] ?; rewrite /= 1?delete_commute. }
  induction e=> vs; simplify_map_eq; auto with f_equal.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end. by case (vs !! _); simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !Hins // !Hdel. eauto with f_equal.
    + by rewrite /= delete_insert_delete delete_idemp.
    + by rewrite /= Hins // delete_insert_delete !Hdel delete_idemp.
Qed.
Lemma subst_map_binder_insert b v vs e :
  subst_map (binder_insert b v vs) e =
  subst' b v (subst_map (binder_delete b vs) e).
Proof. destruct b; rewrite ?subst_map_insert //. Qed.
