From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl list gmap.
From iris.base_logic.lib Require Export own.
From iris Require Import options.
Import uPred.

Local Notation proph_map P V := (gmap P (list V)).
Definition proph_val_list (P V : Type) := list (P * V).

Definition proph_mapUR (P V : Type) `{Countable P} : ucmraT :=
  gmapUR P $ exclR $ listO $ leibnizO V.

Definition to_proph_map {P V} `{Countable P} (pvs : proph_map P V) : proph_mapUR P V :=
  fmap (λ vs, Excl (vs : list (leibnizO V))) pvs.

(** The CMRA we need. *)
Class proph_mapG (P V : Type) (Σ : gFunctors) `{Countable P} := ProphMapG {
  proph_map_inG :> inG Σ (authR (proph_mapUR P V));
  proph_map_name : gname
}.
Arguments proph_map_name {_ _ _ _ _} _ : assert.

Class proph_mapPreG (P V : Type) (Σ : gFunctors) `{Countable P} :=
  { proph_map_preG_inG :> inG Σ (authR (proph_mapUR P V)) }.

Definition proph_mapΣ (P V : Type) `{Countable P} : gFunctors :=
  #[GFunctor (authR (proph_mapUR P V))].

Instance subG_proph_mapPreG {Σ P V} `{Countable P} :
  subG (proph_mapΣ P V) Σ → proph_mapPreG P V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{pG : proph_mapG P V Σ}.
  Implicit Types pvs : proph_val_list P V.
  Implicit Types R : proph_map P V.
  Implicit Types p : P.

  (** The list of resolves for [p] in [pvs]. *)
  Fixpoint proph_list_resolves pvs p : list V :=
    match pvs with
    | []         => []
    | (q,v)::pvs => if decide (p = q) then v :: proph_list_resolves pvs p
                    else proph_list_resolves pvs p
    end.

  Definition proph_resolves_in_list R pvs :=
    map_Forall (λ p vs, vs = proph_list_resolves pvs p) R.

  Definition proph_map_ctx pvs (ps : gset P) : iProp Σ :=
    (∃ R, ⌜proph_resolves_in_list R pvs ∧
          dom (gset _) R ⊆ ps⌝ ∗
          own (proph_map_name pG) (● (to_proph_map R)))%I.

  Definition proph_def (p : P) (vs : list V) : iProp Σ :=
    own (proph_map_name pG) (◯ {[p := Excl vs]}).

  Definition proph_aux : seal (@proph_def). Proof. by eexists. Qed.
  Definition proph := proph_aux.(unseal).
  Definition proph_eq : @proph = @proph_def := proph_aux.(seal_eq).
End definitions.

Section list_resolves.
  Context {P V : Type} `{Countable P}.
  Implicit Type pvs : proph_val_list P V.
  Implicit Type p : P.
  Implicit Type R : proph_map P V.

  Lemma resolves_insert pvs p R :
    proph_resolves_in_list R pvs →
    p ∉ dom (gset _) R →
    proph_resolves_in_list (<[p := proph_list_resolves pvs p]> R) pvs.
  Proof.
    intros Hinlist Hp q vs HEq.
    destruct (decide (p = q)) as [->|NEq].
    - rewrite lookup_insert in HEq. by inversion HEq.
    - rewrite lookup_insert_ne in HEq; last done. by apply Hinlist.
  Qed.
End list_resolves.

Section to_proph_map.
  Context (P V : Type) `{Countable P}.
  Implicit Types p : P.
  Implicit Types vs : list V.
  Implicit Types R : proph_map P V.

  Lemma to_proph_map_valid R : ✓ to_proph_map R.
  Proof. intros l. rewrite lookup_fmap. by case (R !! l). Qed.

  Lemma to_proph_map_insert p vs R :
    to_proph_map (<[p := vs]> R) = <[p := Excl (vs: list (leibnizO V))]> (to_proph_map R).
  Proof. by rewrite /to_proph_map fmap_insert. Qed.

  Lemma to_proph_map_delete p R :
    to_proph_map (delete p R) = delete p (to_proph_map R).
  Proof. by rewrite /to_proph_map fmap_delete. Qed.

  Lemma lookup_to_proph_map_None R p :
    R !! p = None → to_proph_map R !! p = None.
  Proof. by rewrite /to_proph_map lookup_fmap=> ->. Qed.

  Lemma proph_map_singleton_included R p vs :
    {[p := Excl vs]} ≼ to_proph_map R → R !! p = Some vs.
  Proof.
    rewrite singleton_included_exclusive_l; last by apply to_proph_map_valid.
    by rewrite leibniz_equiv_iff /to_proph_map lookup_fmap fmap_Some=> -[v' [-> [->]]].
  Qed.
End to_proph_map.

Lemma proph_map_init `{Countable P, !proph_mapPreG P V PVS} pvs ps :
  ⊢ |==> ∃ _ : proph_mapG P V PVS, proph_map_ctx pvs ps.
Proof.
  iMod (own_alloc (● to_proph_map ∅)) as (γ) "Hh".
  { rewrite auth_auth_valid. exact: to_proph_map_valid. }
  iModIntro. iExists (ProphMapG P V PVS _ _ _ γ), ∅. iSplit; last by iFrame.
  iPureIntro. split =>//.
Qed.

Section proph_map.
  Context `{proph_mapG P V Σ}.
  Implicit Types p : P.
  Implicit Types v : V.
  Implicit Types vs : list V.
  Implicit Types R : proph_map P V.
  Implicit Types ps : gset P.

  (** General properties of mapsto *)
  Global Instance proph_timeless p vs : Timeless (proph p vs).
  Proof. rewrite proph_eq /proph_def. apply _. Qed.

  Lemma proph_exclusive p vs1 vs2 :
    proph p vs1 -∗ proph p vs2 -∗ False.
  Proof.
    rewrite proph_eq /proph_def. iIntros "Hp1 Hp2".
    iCombine "Hp1 Hp2" as "Hp".
    iDestruct (own_valid with "Hp") as %Hp.
    (* FIXME: FIXME(Coq #6294): needs new unification *)
    move:Hp. rewrite auth_frag_valid singleton_valid //.
  Qed.

  Lemma proph_map_new_proph p ps pvs :
    p ∉ ps →
    proph_map_ctx pvs ps ==∗
    proph_map_ctx pvs ({[p]} ∪ ps) ∗ proph p (proph_list_resolves pvs p).
  Proof.
    iIntros (Hp) "HR". iDestruct "HR" as (R) "[[% %] H●]".
    rewrite proph_eq /proph_def.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc, (alloc_singleton_local_update _ p (Excl _))=> //.
      apply lookup_to_proph_map_None.
      apply (not_elem_of_dom (D:=gset P)). set_solver. }
    iModIntro. iFrame.
    iExists (<[p := proph_list_resolves pvs p]> R). iSplitR "H●".
    - iPureIntro. split.
      + apply resolves_insert; first done. set_solver.
      + rewrite dom_insert. set_solver.
    - by rewrite /to_proph_map fmap_insert.
  Qed.

  Lemma proph_map_resolve_proph p v pvs ps vs :
    proph_map_ctx ((p,v) :: pvs) ps ∗ proph p vs ==∗
    ∃vs', ⌜vs = v::vs'⌝ ∗ proph_map_ctx pvs ps ∗ proph p vs'.
  Proof.
    iIntros "[HR Hp]". iDestruct "HR" as (R) "[HP H●]". iDestruct "HP" as %[Hres Hdom].
    rewrite /proph_map_ctx proph_eq /proph_def.
    iDestruct (own_valid_2 with "H● Hp") as %[HR%proph_map_singleton_included _]%auth_both_valid.
    assert (vs = v :: proph_list_resolves pvs p) as ->.
    { rewrite (Hres p vs HR). simpl. by rewrite decide_True. }
    iMod (own_update_2 with "H● Hp") as "[H● H◯]".
    { (* FIXME: FIXME(Coq #6294): needs new unification *)
      eapply auth_update. apply: singleton_local_update.
      - by rewrite /to_proph_map lookup_fmap HR.
      - by apply (exclusive_local_update _ (Excl (proph_list_resolves pvs p : list (leibnizO V)))). }
    rewrite /to_proph_map -fmap_insert.
    iModIntro. iExists (proph_list_resolves pvs p). iFrame. iSplitR.
    - iPureIntro. done.
    - iExists _. iFrame. iPureIntro. split.
      + intros q ws HEq. destruct (decide (p = q)) as [<-|NEq].
        * rewrite lookup_insert in HEq. by inversion HEq.
        * rewrite lookup_insert_ne in HEq; last done.
          rewrite (Hres q ws HEq).
          simpl. rewrite decide_False; done.
      + assert (p ∈ dom (gset P) R) by exact: elem_of_dom_2.
        rewrite dom_insert. set_solver.
  Qed.
End proph_map.
