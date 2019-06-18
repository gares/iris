From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(* Defines compare-and-set (CASet) on top of compare-and-swap (CAS). *)

Definition compare_and_set : val :=
  λ: "l" "v1" "v2", CAS "l" "v1" "v2" = "v1".

Section proof.
  Context `{!heapG Σ}.

  (* This is basically a logically atomic spec, but stronger and hence easier to apply. *)
  Lemma caset_spec (l : loc) (v1 v2 : val) Φ E :
    val_is_unboxed v1 →
    (|={⊤,E}=> ∃ v, l ↦ v ∗ let b := bool_decide (val_for_compare v = val_for_compare v1) in
        (l ↦ (if b then v2 else v) ={E,⊤}=∗ Φ #b) ) -∗
    WP compare_and_set #l v1 v2 @ ⊤ {{ Φ }}.
  Proof.
    iIntros (?) "AU". wp_lam. wp_pures. wp_bind (CAS _ _ _).
    iMod "AU" as (v) "[H↦ Hclose]". case_bool_decide.
    - wp_cas_suc. iMod ("Hclose" with "H↦"). iModIntro. wp_op.
      rewrite bool_decide_true //.
    - wp_cas_fail. iMod ("Hclose" with "H↦"). iModIntro. wp_op.
      rewrite bool_decide_false //.
  Qed.
End proof.
