(** Camera of discardable fractions.

    This is a generalisation of the fractional camera where elements can
    represent both ownership of a fraction (as in the fractional camera) and the
    knowledge that a fraction has been discarded.

    Ownership of a fraction is denoted [DfracOwn q] and behaves identically to
    [q] of the fractional camera.

    Knowledge that a fraction has been discarded is denoted [DfracDiscarded p].
    Elements of this form are their own core, making ownership of them
    persistent. Resource composition combines knowledge that [p] and [p'] have been
    discarded into the knowledge that [p max p'] has been discarded.

    One can make a frame preserving update from _owning_ a fraction to _knowing_
    that the fraction has been discarded.

    Crucially, ownership over 1 is an exclusive element just as it is in the
    fractional camera. Hence owning 1 implies that no fraction has been
    discarded. Conversely, knowing that a fraction has been discarded implies
    that no one can own 1. And, since discarding is an irreversible operation, it
    also implies that no one can own 1 in the future *)
From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export cmra proofmode_classes updates.
From iris Require Import options.

(** An element of dfrac denotes ownership of a fraction, knowledge that a
    fraction has been discarded, or both. Note that all elements can be written
    on the form [DfracOwn q ⋅ DfracDiscarded p]. This should be used instead
    of [DfracBoth] which is for internal use only. *)
Inductive dfrac :=
  | DfracOwn : Qp → dfrac
  | DfracDiscarded : Qp → dfrac
  | DfracBoth : Qp → Qp → dfrac.

Global Instance DfracOwn_inj : Inj (=) (=) DfracOwn.
Proof. by injection 1. Qed.

Global Instance DfracDiscarded_inj : Inj (=) (=) DfracDiscarded.
Proof. by injection 1. Qed.

Global Instance DfracBoth_inj : Inj2 (=) (=) (=) DfracBoth.
Proof. by injection 1. Qed.

Section dfrac.

  Canonical Structure dfracO := leibnizO dfrac.

  Implicit Types p q : Qp.

  Implicit Types x y : dfrac.

  (** An element is valid as long as the sum of its content is less than one. *)
  Instance dfrac_valid : Valid dfrac := λ x,
    match x with
    | DfracOwn q => q ≤ 1%Qp
    | DfracDiscarded p => p ≤ 1%Qp
    | DfracBoth q p => (q + p)%Qp ≤ 1%Qp
    end%Qc.

  (** As in the fractional camera the core is undefined for elements denoting
     ownership of a fraction. For elements denoting the knowledge that a fraction has
     been discarded the core is the identity function. *)
  Instance dfrac_pcore : PCore dfrac := λ x,
    match x with
    | DfracOwn q => None
    | DfracDiscarded p => Some (DfracDiscarded p)
    | DfracBoth q p => Some (DfracDiscarded p)
    end.

  (** When elements are combined, ownership is added together and knowledge of
     discarded fractions is combined with the max operation. *)
  Instance dfrac_op : Op dfrac := λ x y,
    match x, y with
    | DfracOwn q, DfracOwn q' => DfracOwn (q + q')
    | DfracOwn q, DfracDiscarded p' => DfracBoth q p'
    | DfracOwn q, DfracBoth q' p' => DfracBoth (q + q') p'
    | DfracDiscarded p, DfracOwn q' => DfracBoth q' p
    | DfracDiscarded p, DfracDiscarded p' => DfracDiscarded (p `max` p')
    | DfracDiscarded p, DfracBoth q' p' => DfracBoth q' (p `max` p')
    | DfracBoth q p, DfracOwn q' => DfracBoth (q + q') p
    | DfracBoth q p, DfracDiscarded p' => DfracBoth q (p `max` p')
    | DfracBoth q p, DfracBoth q' p' => DfracBoth (q + q') (p `max` p')
    end.

  Lemma dfrac_op_own q p : DfracOwn p ⋅ DfracOwn q = DfracOwn (p + q).
  Proof. done. Qed.

  Lemma dfrac_op_discarded q p :
    DfracDiscarded p ⋅ DfracDiscarded q = DfracDiscarded (p `max` q).
  Proof. done. Qed.

  Lemma dfrac_own_included q p : DfracOwn q ≼ DfracOwn p ↔ (q < p)%Qc.
  Proof.
    rewrite Qp_lt_sum. split.
    - rewrite /included /op /dfrac_op. intros [[o|?|?] [= ->]]. by exists o.
    - intros [o ->]. exists (DfracOwn o). by rewrite dfrac_op_own.
  Qed.

  Lemma dfrac_discarded_included q p :
    DfracDiscarded q ≼ DfracDiscarded p ↔ (q ≤ p)%Qc.
  Proof. 
    split.
    - rewrite /included /op /dfrac_op. intros [[?|?|?] [= ->]]. apply Qp_le_max_l.
    - intros ?. exists (DfracDiscarded p).
      by rewrite dfrac_op_discarded /Qp_max decide_True.
  Qed.

  Definition dfrac_ra_mixin : RAMixin dfrac.
  Proof.
    split; try apply _.
    - intros [?|?|??] y cx <-; intros [= <-]; eexists _; done.
    - intros [?|?|??] [?|?|??] [?|?|??];
        rewrite /op /dfrac_op 1?assoc 1?assoc; done.
    - intros [?|?|??] [?|?|??];
        rewrite /op /dfrac_op 1?(comm Qp_plus) 1?(comm Qp_max); done.
    - intros [?|?|??] cx; rewrite /pcore /dfrac_pcore; intros [= <-];
        rewrite /op /dfrac_op Qp_max_id; done.
    - intros [?|?|??] ? [= <-]; done.
    - intros [?|?|??] [?|?|??] ? [[?|?|??] [=]] [= <-]; eexists _; split; try done;
        apply dfrac_discarded_included; subst; auto; apply Qp_le_max_l.
    - intros [q|p|q p] [q'|p'|q' p']; rewrite /op /dfrac_op /valid /dfrac_valid.
      * apply (Qp_plus_weak_r _ _ 1).
      * apply (Qp_plus_weak_r _ _ 1).
      * apply Qcle_trans. etrans; last apply Qp_le_plus_l. apply Qp_le_plus_l.
      * apply (Qp_plus_weak_l _ _ 1).
      * apply (Qp_max_lub_l _ _ 1).
      * by intros ?%(Qp_plus_weak_l _ _ 1)%(Qp_max_lub_l _ _ 1).
      * rewrite (comm _ _ q') -assoc. apply (Qp_plus_weak_l _ _ 1).
      * intros H. etrans; last apply H.
        apply Qcplus_le_mono_l. apply Qp_le_max_l.
      * intros H. etrans; last apply H.
        rewrite -assoc. apply Qcplus_le_mono_l, Qp_plus_weak_2_r, Qp_le_max_l.
  Qed.
  Canonical Structure dfracR := discreteR dfrac dfrac_ra_mixin.

  Global Instance dfrac_cmra_discrete : CmraDiscrete dfracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance dfrac_full_exclusive : Exclusive (DfracOwn 1).
  Proof.
    intros [q|p|q p];
      rewrite /op /cmra_op -cmra_discrete_valid_iff /valid /cmra_valid /=.
    - apply (Qp_not_plus_ge 1 q).
    - apply (Qp_not_plus_ge 1 p).
    - rewrite -Qcplus_assoc. apply (Qp_not_plus_ge 1 (q + p)).
  Qed.

  Global Instance dfrac_cancelable q : Cancelable (DfracOwn q).
  Proof.
    apply: discrete_cancelable.
    intros [q1|p1|q1 p1][q2|p2|q2 p2] _; rewrite /op /cmra_op; simpl;
      try by intros [= ->].
    - by intros ->%(inj _)%(inj _).
    - by intros [?%symmetry%Qp_plus_id_free _]%(inj2 _).
    - by intros [?%Qp_plus_id_free ?]%(inj2 _).
    - by intros [->%(inj _) ->]%(inj2 _).
  Qed.

  Global Instance frac_id_free q : IdFree (DfracOwn q).
  Proof.
    intros [q'|p'|q' p'] _; rewrite /op /cmra_op; simpl; try by intros [=].
    by intros [= ?%Qp_plus_id_free].
  Qed.

  Global Instance dfrac_discarded_core_id p : CoreId (DfracDiscarded p).
  Proof. by constructor. Qed.

  Lemma dfrac_valid_own p : ✓ DfracOwn p ↔ (p ≤ 1%Qp)%Qc.
  Proof. done. Qed.

  Lemma dfrac_valid_discarded p : ✓ DfracDiscarded p ↔ (p ≤ 1%Qp)%Qc.
  Proof. done. Qed.

  Lemma dfrac_valid_own_discarded q p :
    ✓ (DfracOwn q ⋅ DfracDiscarded p) ↔ (q + p ≤ 1%Qp)%Qc.
  Proof. done. Qed.

  Global Instance is_op_frac q : IsOp' (DfracOwn q) (DfracOwn (q/2)) (DfracOwn (q/2)).
  Proof. by rewrite /IsOp' /IsOp dfrac_op_own Qp_div_2. Qed.

  (** Discarding a fraction is a frame preserving update. *)
  Lemma dfrac_discard_update q : DfracOwn q ~~> DfracDiscarded q.
  Proof.
    intros n [[q'|p'|q' p']|];
      rewrite /op /cmra_op -!cmra_discrete_valid_iff /valid /cmra_valid /=.
    - by rewrite Qcplus_comm.
    - intro. etrans. apply Qp_max_plus. done.
    - intro. etrans; last done.
      rewrite -Qcplus_assoc. rewrite (Qcplus_comm q _). rewrite -Qcplus_assoc.
      apply Qcplus_le_mono_l. rewrite Qcplus_comm. apply Qp_max_plus.
    - done.
  Qed.

End dfrac.