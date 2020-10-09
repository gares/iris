(** Camera of discardable fractions.

    This is a generalisation of the fractional camera where elements can
    represent both ownership of a fraction (as in the fractional camera) and the
    knowledge that a fraction has been discarded.

    Ownership of a fraction is denoted [DfracOwn q] and behaves identically to
    [q] of the fractional camera.

    Knowledge that a fraction has been discarded is denoted [DfracDiscarded].
    This elements is its own core, making ownership persistent.

    One can make a frame preserving update from _owning_ a fraction to _knowing_
    that the fraction has been discarded.

    Crucially, ownership over 1 is an exclusive element just as it is in the
    fractional camera. Hence owning 1 implies that no fraction has been
    discarded. Conversely, knowing that a fraction has been discarded implies
    that no one can own 1. And, since discarding is an irreversible operation,
    it also implies that no one can own 1 in the future *)
From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates frac.
From iris Require Import options.

(** An element of dfrac denotes ownership of a fraction, knowledge that a
    fraction has been discarded, or both. Note that [DfracBoth] can be written
    as [DfracOwn q ⋅ DfracDiscarded]. This should be used instead
    of [DfracBoth] which is for internal use only. *)
Inductive dfrac :=
  | DfracOwn : Qp → dfrac
  | DfracDiscarded : dfrac
  | DfracBoth : Qp → dfrac.

Global Instance DfracOwn_inj : Inj (=) (=) DfracOwn.
Proof. by injection 1. Qed.

Global Instance DfracBoth_inj : Inj (=) (=) DfracBoth.
Proof. by injection 1. Qed.

Section dfrac.

  Canonical Structure dfracO := leibnizO dfrac.

  Implicit Types p q : Qp.

  Implicit Types x y : dfrac.

  (** An element is valid as long as the sum of its content is less than one. *)
  Instance dfrac_valid : Valid dfrac := λ x,
    match x with
    | DfracOwn q => q ≤ 1%Qp
    | DfracDiscarded => True
    | DfracBoth q => q < 1%Qp
    end%Qc.

  (** As in the fractional camera the core is undefined for elements denoting
     ownership of a fraction. For elements denoting the knowledge that a fraction has
     been discarded the core is the identity function. *)
  Instance dfrac_pcore : PCore dfrac := λ x,
    match x with
    | DfracOwn q => None
    | DfracDiscarded => Some DfracDiscarded
    | DfracBoth q => Some DfracDiscarded
    end.

  (** When elements are combined, ownership is added together and knowledge of
     discarded fractions is combined with the max operation. *)
  Instance dfrac_op : Op dfrac := λ x y,
    match x, y with
    | DfracOwn q, DfracOwn q' => DfracOwn (q + q')
    | DfracOwn q, DfracDiscarded => DfracBoth q
    | DfracOwn q, DfracBoth q' => DfracBoth (q + q')
    | DfracDiscarded, DfracOwn q' => DfracBoth q'
    | DfracDiscarded, DfracDiscarded => DfracDiscarded
    | DfracDiscarded, DfracBoth q' => DfracBoth q'
    | DfracBoth q, DfracOwn q' => DfracBoth (q + q')
    | DfracBoth q, DfracDiscarded => DfracBoth q
    | DfracBoth q, DfracBoth q' => DfracBoth (q + q')
    end.

  Lemma dfrac_op_own q p : DfracOwn p ⋅ DfracOwn q = DfracOwn (p + q).
  Proof. done. Qed.

  Lemma dfrac_op_discarded :
    DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_own_included q p : DfracOwn q ≼ DfracOwn p ↔ (q < p)%Qc.
  Proof.
    rewrite Qp_lt_sum. split.
    - rewrite /included /op /dfrac_op. intros [[o| |?] [= ->]]. by exists o.
    - intros [o ->]. exists (DfracOwn o). by rewrite dfrac_op_own.
  Qed.

  (* [dfrac] does not have a unit so reflexivity is not for granted! *)
  Lemma dfrac_discarded_included :
    DfracDiscarded ≼ DfracDiscarded.
  Proof. exists DfracDiscarded. done. Qed.

  Definition dfrac_ra_mixin : RAMixin dfrac.
  Proof.
    split; try apply _.
    - intros [?| |?] y cx <-; intros [= <-]; eexists _; done.
    - intros [?| |?] [?| |?] [?| |?];
        rewrite /op /dfrac_op 1?assoc 1?assoc; done.
    - intros [?| |?] [?| |?];
        rewrite /op /dfrac_op 1?(comm Qp_plus); done.
    - intros [?| |?] cx; rewrite /pcore /dfrac_pcore; intros [= <-];
        rewrite /op /dfrac_op; done.
    - intros [?| |?] ? [= <-]; done.
    - intros [?| |?] [?| |?] ? [[?| |?] [=]] [= <-]; eexists _; split; try done;
        apply dfrac_discarded_included.
    - intros [q| |q] [q'| |q']; rewrite /op /dfrac_op /valid /dfrac_valid; try done.
      * apply (Qp_plus_weak_r _ _ 1).
      * apply Qclt_le_weak.
      * move=> /Qclt_le_weak. apply Qcle_trans. etrans; last apply Qp_le_plus_l. done.
      * apply Qclt_trans. apply Qp_lt_sum. eauto.
      * apply Qclt_trans. apply Qp_lt_sum. eauto.
  Qed.
  Canonical Structure dfracR := discreteR dfrac dfrac_ra_mixin.

  Global Instance dfrac_cmra_discrete : CmraDiscrete dfracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance dfrac_full_exclusive : Exclusive (DfracOwn 1).
  Proof.
    intros [q| |q];
      rewrite /op /cmra_op -cmra_discrete_valid_iff /valid /cmra_valid /=.
    - apply (Qp_not_plus_ge 1 q).
    - intros []%(irreflexivity _).
    - move=> /Qclt_le_weak. apply (Qp_not_plus_ge 1 q).
  Qed.

  Global Instance dfrac_cancelable q : Cancelable (DfracOwn q).
  Proof.
    apply: discrete_cancelable.
    intros [q1| |q1] [q2| |q2] _; rewrite /op /cmra_op; simpl;
      try by intros [= ->].
    - by intros ->%(inj _)%(inj _).
    - done.
    - intros Hq%(inj _). symmetry in Hq. apply Qp_plus_id_free in Hq. done.
    - by intros Hq%(inj _)%Qp_plus_id_free.
    - by intros ->%(inj _)%(inj _).
  Qed.

  Global Instance frac_id_free q : IdFree (DfracOwn q).
  Proof.
    intros [q'| |q'] _; rewrite /op /cmra_op; simpl; try by intros [=].
    by intros [= ?%Qp_plus_id_free].
  Qed.

  Global Instance dfrac_discarded_core_id : CoreId DfracDiscarded.
  Proof. by constructor. Qed.

  Lemma dfrac_valid_own p : ✓ DfracOwn p ↔ (p ≤ 1%Qp)%Qc.
  Proof. done. Qed.

  Lemma dfrac_valid_discarded p : ✓ DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_valid_own_discarded q :
    ✓ (DfracOwn q ⋅ DfracDiscarded) ↔ (q < 1%Qp)%Qc.
  Proof. done. Qed.

  Global Instance dfrac_is_op q q1 q2 :
    IsOp q q1 q2 →
    IsOp' (DfracOwn q) (DfracOwn q1) (DfracOwn q2).
  Proof. rewrite /IsOp' /IsOp dfrac_op_own=>-> //. Qed.

  (** Discarding a fraction is a frame preserving update. *)
  Lemma dfrac_discard_update q : DfracOwn q ~~> DfracDiscarded.
  Proof.
    intros n [[q'| |q']|];
      rewrite /op /cmra_op -!cmra_discrete_valid_iff /valid /cmra_valid /=.
    - intros [Hq|Hq]%Qcle_lt_or_eq.
      + etrans; last eassumption. change (q' < (q + q')%Qp)%Qc. apply Qp_lt_sum.
        rewrite {1}comm. eauto.
      + change (q' < 1%Qp)%Qc. apply Qp_lt_sum. exists q.
        rewrite (comm Qp_plus). apply Qp_eq. simpl. rewrite Hq. done.
    - done.
    - apply Qclt_trans. change (q' < (q + q')%Qp)%Qc. apply Qp_lt_sum.
      rewrite {1}comm. eauto.
    - done.
  Qed.

End dfrac.
