From iris.algebra Require Import base.
From stdpp Require Import countable numbers gmap.

Record loc := { loc_car : Z }.

Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Qed.

Instance loc_inhabited : Inhabited loc := populate {|loc_car := 0 |}.

Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' loc_car (λ i, {| loc_car := i |})); intros []. Qed.

Program Definition loc_infinite : Infinite loc := {|
  infinite_fresh l := {| loc_car := infinite_fresh (loc_car <$> l) |}
|}.
Next Obligation.
  intros xs Hfresh. unfold fresh in Hfresh.
  eapply (infinite_is_fresh (loc_car <$> xs)).
  eapply elem_of_list_fmap. eexists. split; last done.
  reflexivity.
Qed.
Next Obligation.
  intros xs ys Hperm. unfold fresh. f_equal.
  eapply infinite_fresh_Permutation. rewrite Hperm //.
Qed.

Definition loc_add (l : loc) (off : Z) : loc :=
  {| loc_car := loc_car l + off|}.

Notation "l +ₗ off" := (loc_add l off) (at level 50, left associativity).

Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Lemma loc_add_0 l : l +ₗ 0 = l.
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Instance loc_add_inj l : Inj eq eq (loc_add l).
Proof. destruct l; rewrite /Inj /loc_add /=; intros; simplify_eq; lia. Qed.

Definition fresh_locs (g : gset loc) (n : Z) : loc :=
  {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r)%Z 1%Z g |}.

Lemma fresh_locs_fresh g n i :
  (0 ≤ i)%Z → (i < n)%Z → (fresh_locs g n) +ₗ i ∉ g.
Proof.
  rewrite /fresh_locs /loc_add /=; intros Hil _ Hf; clear n.
  cut (∀ x, x ∈ g →
            loc_car x < set_fold (λ k r, ((1 + loc_car k) `max` r)%Z) 1%Z g)%Z.
  { intros Hlem; apply Hlem in Hf; simpl in *; lia. }
  clear Hf.
  eapply (set_fold_ind_L
            (λ z g, ∀ x : loc, x ∈ g → (loc_car x < z)%Z));
    try set_solver by eauto with lia.
Qed.

Global Opaque fresh_locs.
