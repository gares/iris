From iris.base_logic.lib Require Import invariants.

(** Make sure that the same [Equivalence] instance is picked for Leibniz OFEs
with carriers that are definitionally equal. See also
https://gitlab.mpi-sws.org/iris/iris/issues/299 *)
Definition tag := nat.
Canonical Structure tagO := leibnizO tag.
Goal tagO = natO.
Proof. reflexivity. Qed.

Instance test_cofe {Σ} : Cofe (iPrePropO Σ) := _.

Section tests.
  Context `{!invG Σ}.

  Program Definition test : (iPropO Σ -n> iPropO Σ) -n> (iPropO Σ -n> iPropO Σ) :=
    λne P v, (▷ (P v))%I.
  Solve Obligations with solve_proper.

End tests.

(** Check that [@Reflexive Prop ?r] picks the instance setoid_rewrite needs.
    Really, we want to set [Hint Mode Reflexive] in a way that this fails, but
    we cannot [1].  So at least we try to make sure the first solution found
    is the right one, to not pay performance in the success case [2].

    [1] https://github.com/coq/coq/issues/7916
    [2] https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp/merge_requests/38
*)
Lemma test_setoid_rewrite :
  ∃ R, @Reflexive Prop R ∧ R = iff.
Proof.
  eexists. split.
  - apply _.
  - reflexivity.
Qed.
