(** Coq configuration for Iris (not meant to leak to clients) *)
(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

Export Set Default Proof Using "Type".
Export Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)
